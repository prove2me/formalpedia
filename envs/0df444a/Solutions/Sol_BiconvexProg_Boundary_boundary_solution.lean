-- Prove2me | solution 1 for BiconvexProg.Boundary.boundary_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:41:52.046806+00:00
-- url     : https://prove2.me/submissions/4ccc5e79-ecb5-49dc-ba0b-7b0d7a9c40ef

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_BiconcaveOn

theorem biconvexBoundary_exit_point {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : Set X} (hS : IsCompact S) {z : X} (hz : z ∈ interior S) {w : X} (hw : w ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ s : ℝ, 0 ≤ s → s ≤ t → z + s • w ∈ S) ∧ z + t • w ∈ frontier S := by
  have hSc : IsClosed S := hS.isClosed
  set g : ℝ → X := fun t => z + t • w with hgdef
  have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  set K : Set ℝ := Set.Ici 0 ∩ (g ⁻¹' interior S)ᶜ with hKdef
  have hKc : IsClosed K := isClosed_Ici.inter (isOpen_interior.preimage hg).isClosed_compl
  have hzS : z ∈ S := interior_subset hz
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  have hRz : ‖z‖ ≤ R := hR z hzS
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hKne : K.Nonempty := by
    refine ⟨(R + ‖z‖ + 1) / ‖w‖, ?_, ?_⟩
    · show 0 ≤ (R + ‖z‖ + 1) / ‖w‖
      exact div_nonneg (by linarith [norm_nonneg z]) hwpos.le
    · intro hmem
      have hin : g ((R + ‖z‖ + 1) / ‖w‖) ∈ S := interior_subset hmem
      have h1 := hR _ hin
      have h2 : ‖((R + ‖z‖ + 1) / ‖w‖) • w‖ = R + ‖z‖ + 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith [norm_nonneg z]) hwpos.le)]
        field_simp
      have h3 : ‖((R + ‖z‖ + 1) / ‖w‖) • w‖ ≤ ‖z + ((R + ‖z‖ + 1) / ‖w‖) • w‖ + ‖z‖ := by
        have := norm_sub_le (z + ((R + ‖z‖ + 1) / ‖w‖) • w) z
        simpa using this
      simp only [hgdef] at h1
      linarith
  have hKb : BddBelow K := ⟨0, fun t ht => ht.1⟩
  set t0 := sInf K with ht0def
  have ht0 : t0 ∈ K := hKc.csInf_mem hKne hKb
  have ht0pos : 0 < t0 := by
    rcases lt_or_eq_of_le (Set.mem_Ici.mp ht0.1) with h | h
    · exact h
    · exfalso
      apply ht0.2
      show g t0 ∈ interior S
      rw [← h]
      simpa [hgdef] using hz
  have hlt : ∀ s : ℝ, 0 ≤ s → s < t0 → g s ∈ interior S := by
    intro s hs hst
    by_contra hns
    have : s ∈ K := ⟨hs, hns⟩
    have := csInf_le hKb this
    linarith
  have hgt0 : g t0 ∈ S := by
    have hcl : t0 ∈ closure (Set.Ico 0 t0) := by
      rw [closure_Ico (ne_of_lt ht0pos)]
      exact ⟨ht0pos.le, le_rfl⟩
    have := map_mem_closure hg hcl (fun s hs => interior_subset (hlt s hs.1 hs.2))
    rwa [hSc.closure_eq] at this
  refine ⟨t0, ht0pos, ?_, ?_⟩
  · intro s hs hst
    rcases lt_or_eq_of_le hst with h | h
    · exact interior_subset (hlt s hs h)
    · rw [h]; exact hgt0
  · rw [hSc.frontier_eq]
    exact ⟨hgt0, ht0.2⟩

theorem biconvexBoundary_line_min {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : Set X} (hS : IsCompact S) (φ : X → ℝ) {z0 : X} (hz0 : z0 ∈ interior S)
    (hmin : IsMinOn φ S z0) {w : X} (hw : w ≠ 0)
    (hconc : ∀ a b : ℝ, 0 < a → 0 < b → (∀ s : ℝ, -a ≤ s → s ≤ b → z0 + s • w ∈ S) →
      b / (a + b) * φ (z0 + (-a) • w) + a / (a + b) * φ (z0 + b • w) ≤ φ z0) :
    ∃ z ∈ frontier S, IsMinOn φ S z := by
  obtain ⟨b, hb, hbS, hbF⟩ := biconvexBoundary_exit_point hS hz0 hw
  obtain ⟨a, ha, haS, -⟩ := biconvexBoundary_exit_point hS hz0 (neg_ne_zero.mpr hw)
  have hseg : ∀ s : ℝ, -a ≤ s → s ≤ b → z0 + s • w ∈ S := by
    intro s h1 h2
    rcases le_total 0 s with h | h
    · exact hbS s h h2
    · have := haS (-s) (by linarith) (by linarith)
      rwa [neg_smul_neg] at this
  have key := hconc a b ha hb hseg
  have hmin' := isMinOn_iff.mp hmin
  have hA : φ z0 ≤ φ (z0 + (-a) • w) := hmin' _ (hseg (-a) le_rfl (by linarith))
  have hB : φ z0 ≤ φ (z0 + b • w) := hmin' _ (hbS b hb.le le_rfl)
  have hab : 0 < a + b := by linarith
  have hα0 : 0 ≤ b / (a + b) := by positivity
  have hβ0 : 0 < a / (a + b) := by positivity
  have hsum : b / (a + b) + a / (a + b) = 1 := by
    rw [← add_div, add_comm b a, div_self hab.ne']
  have hm : b / (a + b) * φ z0 + a / (a + b) * φ z0 = φ z0 := by
    rw [← add_mul, hsum, one_mul]
  have hαA := mul_le_mul_of_nonneg_left hA hα0
  have h1 : a / (a + b) * φ (z0 + b • w) ≤ a / (a + b) * φ z0 := by linarith
  have hB' : φ (z0 + b • w) ≤ φ z0 := le_of_mul_le_mul_left h1 hβ0
  refine ⟨z0 + b • w, hbF, isMinOn_iff.mpr fun z hz => ?_⟩
  exact le_trans hB' (hmin' z hz)

open BiconvexProg.Boundary in
theorem solution {p q : ℕ} (hpq : 0 < p + q)
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)))
    (hS : IsCompact S) (hne : S.Nonempty)
    (φ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hcont : ContinuousOn φ S) (hbi : BiconcaveOn S φ) :
    ∃ z ∈ frontier S, IsMinOn φ S z := by
  obtain ⟨z0, hz0S, hmin⟩ := hS.exists_isMinOn hne hcont
  by_cases hfr : z0 ∈ frontier S
  · exact ⟨z0, hfr, hmin⟩
  have hint : z0 ∈ interior S := by
    rw [hS.isClosed.frontier_eq] at hfr
    by_contra h
    exact hfr ⟨hz0S, h⟩
  obtain ⟨x0, y0⟩ := z0
  have hmin' := isMinOn_iff.mp hmin
  rcases Nat.eq_zero_or_pos p with hp | hp
  · -- y-side
    have hq : 0 < q := by omega
    set v : EuclideanSpace ℝ (Fin q) := PiLp.single 2 (⟨0, hq⟩ : Fin q) (1 : ℝ) with hvdef
    have hv : v ≠ 0 := by
      intro h
      have := PiLp.norm_single 2 (fun _ : Fin q => ℝ) (⟨0, hq⟩ : Fin q) (1 : ℝ)
      rw [← hvdef, h, norm_zero, norm_one] at this
      exact zero_ne_one this
    have hw : ((0 : EuclideanSpace ℝ (Fin p)), v) ≠ 0 := by
      intro h
      exact hv (congrArg Prod.snd h)
    apply biconvexBoundary_line_min hS φ hint hmin hw
    intro a b ha hb hseg
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] at hseg ⊢
    have hab : 0 < a + b := by linarith
    have hmemC : ∀ y ∈ segment ℝ (y0 + (-a) • v) (y0 + b • v), (x0, y) ∈ S := by
      rintro y ⟨α, β, hα, hβ, hαβ, rfl⟩
      have := hseg (β * b - α * a) (by nlinarith) (by nlinarith)
      obtain rfl : α = 1 - β := by linarith
      convert this using 2
      module
    have hC := (hbi.2 x0 _ (convex_segment _ _) hmemC).2
      (left_mem_segment ℝ (y0 + (-a) • v) (y0 + b • v))
      (right_mem_segment ℝ (y0 + (-a) • v) (y0 + b • v))
      (show 0 ≤ b / (a + b) by positivity) (show 0 ≤ a / (a + b) by positivity)
      (show b / (a + b) + a / (a + b) = 1 by rw [← add_div, add_comm b a, div_self hab.ne'])
    have e1 : b / (a + b) + a / (a + b) = 1 := by
      rw [← add_div, add_comm b a, div_self hab.ne']
    have e2 : b / (a + b) * (-a) + a / (a + b) * b = 0 := by ring
    have hpt : (b / (a + b)) • (y0 + (-a) • v) + (a / (a + b)) • (y0 + b • v) = y0 := by
      calc (b / (a + b)) • (y0 + (-a) • v) + (a / (a + b)) • (y0 + b • v)
          = (b / (a + b) + a / (a + b)) • y0 + (b / (a + b) * (-a) + a / (a + b) * b) • v := by
            module
        _ = y0 := by rw [e1, e2, one_smul, zero_smul, add_zero]
    simp only [smul_eq_mul, hpt] at hC
    exact hC
  · -- x-side
    set v : EuclideanSpace ℝ (Fin p) := PiLp.single 2 (⟨0, hp⟩ : Fin p) (1 : ℝ) with hvdef
    have hv : v ≠ 0 := by
      intro h
      have := PiLp.norm_single 2 (fun _ : Fin p => ℝ) (⟨0, hp⟩ : Fin p) (1 : ℝ)
      rw [← hvdef, h, norm_zero, norm_one] at this
      exact zero_ne_one this
    have hw : (v, (0 : EuclideanSpace ℝ (Fin q))) ≠ 0 := by
      intro h
      exact hv (congrArg Prod.fst h)
    apply biconvexBoundary_line_min hS φ hint hmin hw
    intro a b ha hb hseg
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] at hseg ⊢
    have hab : 0 < a + b := by linarith
    have hmemC : ∀ x ∈ segment ℝ (x0 + (-a) • v) (x0 + b • v), (x, y0) ∈ S := by
      rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
      have := hseg (β * b - α * a) (by nlinarith) (by nlinarith)
      obtain rfl : α = 1 - β := by linarith
      convert this using 2
      module
    have hC := (hbi.1 y0 _ (convex_segment _ _) hmemC).2
      (left_mem_segment ℝ (x0 + (-a) • v) (x0 + b • v))
      (right_mem_segment ℝ (x0 + (-a) • v) (x0 + b • v))
      (show 0 ≤ b / (a + b) by positivity) (show 0 ≤ a / (a + b) by positivity)
      (show b / (a + b) + a / (a + b) = 1 by rw [← add_div, add_comm b a, div_self hab.ne'])
    have e1 : b / (a + b) + a / (a + b) = 1 := by
      rw [← add_div, add_comm b a, div_self hab.ne']
    have e2 : b / (a + b) * (-a) + a / (a + b) * b = 0 := by ring
    have hpt : (b / (a + b)) • (x0 + (-a) • v) + (a / (a + b)) • (x0 + b • v) = x0 := by
      calc (b / (a + b)) • (x0 + (-a) • v) + (a / (a + b)) • (x0 + b • v)
          = (b / (a + b) + a / (a + b)) • x0 + (b / (a + b) * (-a) + a / (a + b) * b) • v := by
            module
        _ = x0 := by rw [e1, e2, one_smul, zero_smul, add_zero]
    simp only [smul_eq_mul, hpt] at hC
    exact hC
