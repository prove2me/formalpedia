-- Prove2me | solution 1 for ChenTeboullePMD.Rate.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:51:35.777609+00:00
-- url     : https://prove2.me/submissions/9cf42f6e-1472-4c23-b941-084333985527

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

set_option autoImplicit false

namespace PMD34Aux

open ChenTeboullePMD.Rate BeckTeboulleMD.EMDA Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma subset_closure_ri [FiniteDimensional ℝ E] {C : Set E} (hC : Convex ℝ C)
    (hne : C.Nonempty) : C ⊆ closure (intrinsicInterior ℝ C) := by
  have hne' := hne.coe_sort
  obtain ⟨p, hp⟩ := hne
  let p' : affineSpan ℝ C := ⟨p, subset_affineSpan _ _ hp⟩
  let φ : (affineSpan ℝ C).direction ≃ₜ affineSpan ℝ C :=
    (AffineIsometryEquiv.constVSub ℝ p').symm.toHomeomorph
  let T : Set (affineSpan ℝ C).direction := φ ⁻¹' ((↑) ⁻¹' C : Set (affineSpan ℝ C))
  have hT : Convex ℝ T := hC.affine_preimage ((affineSpan ℝ C).subtype.comp
    (AffineIsometryEquiv.constVSub ℝ p').symm.toAffineEquiv.toAffineMap)
  have hri : (intrinsicInterior ℝ C).Nonempty := Set.Nonempty.intrinsicInterior hC ⟨p, hp⟩
  have hTi : (interior T).Nonempty := by
    rw [intrinsicInterior, Set.image_nonempty] at hri
    obtain ⟨a, ha⟩ := hri
    refine ⟨φ.symm a, ?_⟩
    have : φ ⁻¹' interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) = interior T :=
      φ.preimage_interior _
    rw [← this]
    simpa using ha
  have hcl := hT.closure_interior_eq_closure_of_nonempty_interior hTi
  intro c hc
  let c' : affineSpan ℝ C := ⟨c, subset_affineSpan _ _ hc⟩
  have h1 : φ.symm c' ∈ closure (interior T) := by
    rw [hcl]
    apply subset_closure
    show φ (φ.symm c') ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C))
    simpa using hc
  have h2 : c' ∈ closure (interior ((↑) ⁻¹' C : Set (affineSpan ℝ C))) := by
    have := Set.mem_image_of_mem φ h1
    rw [φ.image_closure, φ.image_interior, φ.image_preimage, φ.apply_symm_apply] at this
    exact this
  exact image_closure_subset_closure_image continuous_subtype_val
    (Set.mem_image_of_mem Subtype.val h2)

lemma small_o_aux (ψ : E → ℝ) (y v : E) (hd : DifferentiableAt ℝ ψ y) (a c : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ t * a + c * (ψ (y + t • v) - ψ y - t * fderiv ℝ ψ y v)) : 0 ≤ a := by
  set g : ℝ → ℝ := fun t => ψ (y + t • v) with hg
  have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  have h2 : HasDerivAt g (fderiv ℝ ψ y v) 0 := by
    have hd' : HasFDerivAt ψ (fderiv ℝ ψ y) (y + (0:ℝ) • v) := by simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0:ℝ) h1
  have h3 := (hasDerivAt_iff_tendsto_slope.1 h2).mono_left
    (nhdsWithin_mono _ (fun t (ht : (0:ℝ) < t) => (show t ≠ 0 from ht.ne')))
  have h4 : Tendsto (fun t => a + c * (slope g 0 t - fderiv ℝ ψ y v)) (𝓝[>] (0:ℝ))
      (𝓝 (a + c * (fderiv ℝ ψ y v - fderiv ℝ ψ y v))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (h3.sub tendsto_const_nhds))
  rw [sub_self, mul_zero, add_zero] at h4
  refine ge_of_tendsto h4 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have ht0 : 0 < t := ht.1
  have hh := h t ht0 ht.2.le
  have hg0 : g 0 = ψ y := by simp [hg]
  rw [slope_def_field, hg0]
  have : a + c * ((g t - ψ y) / (t - 0) - fderiv ℝ ψ y v)
      = (t * a + c * (g t - ψ y - t * fderiv ℝ ψ y v)) / t := by
    have htne : t ≠ 0 := ht0.ne'
    field_simp
    ring
  rw [this]
  exact div_nonneg hh ht0.le

lemma bregman_nonneg' {D : Set E} {ψ : E → ℝ} (hconv : ConvexOn ℝ D ψ) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hd : DifferentiableAt ℝ ψ y) : 0 ≤ bregman ψ x y := by
  apply small_o_aux ψ y (x - y) hd (bregman ψ x y) (-1)
  intro t ht0 ht1
  have hc := hconv.2 hy hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring : 1 - t + t = 1)
  have he : (1 - t) • y + t • x = y + t • (x - y) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [he, smul_eq_mul, smul_eq_mul] at hc
  simp only [bregman]
  nlinarith [hc]

lemma diff_of_mem {S : Set E} {ψ : E → ℝ} (hψ : IsBregmanFunction S ψ) {y : E} (hy : y ∈ S) :
    DifferentiableAt ℝ ψ y :=
  (hψ.contDiffOn.differentiableOn one_ne_zero y hy).differentiableAt (hψ.isOpen.mem_nhds hy)

lemma three_point (ψ : E → ℝ) (u a b : E) :
    bregman ψ u a - bregman ψ u b - bregman ψ b a
      = fderiv ℝ ψ b (u - b) - fderiv ℝ ψ a (u - b) := by
  simp only [bregman]
  rw [show u - a = (u - b) + (b - a) by abel, map_add]
  ring

lemma key {S C : Set E} {ψ f : E → ℝ} {lam : ℕ → ℝ} {x : ℕ → E}
    (hψ : IsBregmanFunction S ψ) (hCconv : Convex ℝ C) (hf : ConvexOn ℝ C f)
    (hrun : IsPMDRun S C ψ f lam x) (k : ℕ) (hl : 0 < lam (k + 1)) (u : E) (hu : u ∈ C)
    (huS : u ∈ closure S) :
    lam (k + 1) * (f (x (k + 1)) - f u) ≤
      bregman ψ u (x k) - bregman ψ u (x (k + 1)) - bregman ψ (x (k + 1)) (x k) := by
  obtain ⟨hyS, hyC, hmin⟩ := hrun.2 k
  have hdy := diff_of_mem hψ hyS
  have hSconv : Convex ℝ (closure S) := hψ.strictConvexOn.1
  set y := x (k + 1) with hydef
  set z := x k with hzdef
  set c := (lam (k + 1))⁻¹ with hc
  have ha : 0 ≤ (f u - f y) + c * (fderiv ℝ ψ y (u - y) - fderiv ℝ ψ z (u - y)) := by
    apply small_o_aux ψ y (u - y) hdy _ c
    intro t ht0 ht1
    have he : (1 - t) • y + t • u = y + t • (u - y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hutC : y + t • (u - y) ∈ C := by
      rw [← he]; exact hCconv hyC hu (by linarith) ht0.le (by ring)
    have hutS : y + t • (u - y) ∈ closure S := by
      rw [← he]; exact hSconv (subset_closure hyS) huS (by linarith) ht0.le (by ring)
    have hm := hmin _ hutC hutS
    have hfc := hf.2 hyC hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    rw [he, smul_eq_mul, smul_eq_mul] at hfc
    have hE : bregman ψ (y + t • (u - y)) z - bregman ψ y z
        = ψ (y + t • (u - y)) - ψ y - t * fderiv ℝ ψ z (u - y) := by
      simp only [bregman]
      rw [show y + t • (u - y) - z = t • (u - y) + (y - z) by abel, map_add, map_smul,
        smul_eq_mul]
      ring
    have hgoal : t * ((f u - f y) + c * (fderiv ℝ ψ y (u - y) - fderiv ℝ ψ z (u - y)))
        + c * (ψ (y + t • (u - y)) - ψ y - t * fderiv ℝ ψ y (u - y))
        = t * (f u - f y) + c * (bregman ψ (y + t • (u - y)) z - bregman ψ y z) := by
      rw [hE]; ring
    rw [hgoal, mul_sub]
    nlinarith [hm, hfc]
  have h3 := three_point ψ u z y
  rw [h3]
  have hlc : lam (k + 1) * c = 1 := mul_inv_cancel₀ hl.ne'
  have hm2 := mul_nonneg hl.le ha
  have hΔ : lam (k + 1) * (c * (fderiv ℝ ψ y (u - y) - fderiv ℝ ψ z (u - y)))
      = fderiv ℝ ψ y (u - y) - fderiv ℝ ψ z (u - y) := by
    rw [← mul_assoc, hlc, one_mul]
  rw [mul_add, hΔ] at hm2
  nlinarith [hm2]

end PMD34Aux

open PMD34Aux

open ChenTeboullePMD.Rate BeckTeboulleMD.EMDA Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    (∀ n, 1 ≤ n → ∀ u ∈ C, u ∈ closure S →
      f (x n) - f u ≤ (sigma lam n)⁻¹ * bregman ψ u (x 0)) ∧
    (Tendsto (sigma lam) atTop atTop →
      Tendsto (fun n => (f (x n) : EReal)) atTop
        (𝓝 (⨅ u ∈ C, (f u : EReal)))) ∧
    (∀ xs, (xs ∈ C ∧ ∀ v ∈ C, f xs ≤ f v) →
      ∀ n, 1 ≤ n →
        f (x n) - f xs ≤ (sigma lam n)⁻¹ * bregman ψ xs (x 0)) ∧
    (Tendsto (sigma lam) atTop atTop →
      (∃ xs, xs ∈ C ∧ ∀ v ∈ C, f xs ≤ f v) →
      ∃ z, (z ∈ C ∧ ∀ v ∈ C, f z ≤ f v) ∧
        Tendsto x atTop (𝓝 z)) := by
  have hψc : ConvexOn ℝ (closure S) ψ := hψ.strictConvexOn.convexOn
  have hCS : C ⊆ closure S := (subset_closure_ri hCconv hCne).trans (closure_mono hri)
  have hD : ∀ a ∈ closure S, ∀ b ∈ S, 0 ≤ bregman ψ a b := fun a ha b hb =>
    bregman_nonneg' hψc ha (subset_closure hb) (diff_of_mem hψ hb)
  have hxS : ∀ n, x n ∈ S := by
    intro n
    cases n with
    | zero => exact hrun.1
    | succ k => exact (hrun.2 k).1
  have hxC : ∀ n, 1 ≤ n → x n ∈ C := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (hrun.2 k).2.1
  have hK : ∀ k, ∀ u ∈ C,
      lam (k + 1) * (f (x (k + 1)) - f u) ≤ bregman ψ u (x k) - bregman ψ u (x (k + 1)) := by
    intro k u hu
    have h1 := key hψ hCconv hf hrun k (hlam _ (by omega)) u hu (hCS hu)
    have h2 := hD _ (subset_closure (hxS (k + 1))) _ (hxS k)
    linarith
  have hmono : ∀ k, f (x (k + 1 + 1)) ≤ f (x (k + 1)) := by
    intro k
    have h := hK (k + 1) (x (k + 1)) (hxC _ (by omega))
    have h0 : bregman ψ (x (k + 1)) (x (k + 1)) = 0 := by simp [bregman]
    rw [h0] at h
    have h2 := hD _ (hCS (hxC (k + 1) (by omega))) _ (hxS (k + 1 + 1))
    have hl := hlam (k + 1 + 1) (by omega)
    by_contra hcon
    push Not at hcon
    have := mul_pos hl (sub_pos.2 hcon)
    linarith
  have hanti : ∀ k n, 1 ≤ k → k ≤ n → f (x n) ≤ f (x k) := by
    have hA : Antitone (fun m => f (x (m + 1))) := antitone_nat_of_succ_le (fun m => hmono m)
    intro k n hk hkn
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact hA (by omega : k' ≤ n')
  have hsig_pos : ∀ n, 1 ≤ n → 0 < sigma lam n := by
    intro n hn
    unfold sigma
    apply Finset.sum_pos
    · intro i hi
      exact hlam i (Finset.mem_Icc.1 hi).1
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hn⟩⟩
  have htele : ∀ u ∈ C, ∀ n, ∑ k ∈ Finset.Icc 1 n, lam k * (f (x k) - f u) ≤
      bregman ψ u (x 0) - bregman ψ u (x n) := by
    intro u hu n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := hK n u hu
      linarith
  have h20 : ∀ n, 1 ≤ n → ∀ u ∈ C, f (x n) - f u ≤ (sigma lam n)⁻¹ * bregman ψ u (x 0) := by
    intro n hn u hu
    have hσ := hsig_pos n hn
    rw [le_inv_mul_iff₀ hσ]
    have h1 : sigma lam n * (f (x n) - f u) ≤ ∑ k ∈ Finset.Icc 1 n, lam k * (f (x k) - f u) := by
      unfold sigma
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
      exact mul_le_mul_of_nonneg_left (by linarith [hanti k n hk1 hkn]) (hlam k hk1).le
    have h2 := htele u hu n
    have h3 := hD u (hCS hu) (x n) (hxS n)
    linarith
  have hval : Tendsto (sigma lam) atTop atTop → ∀ u ∈ C,
      Tendsto (fun n => f u + (sigma lam n)⁻¹ * bregman ψ u (x 0)) atTop (𝓝 (f u)) := by
    intro hσ u _
    have := (hσ.inv_tendsto_atTop).mul_const (bregman ψ u (x 0))
    rw [zero_mul] at this
    simpa using (tendsto_const_nhds (x := f u)).add this
  refine ⟨fun n hn u hu _ => h20 n hn u hu, ?_, fun xs hxs n hn => h20 n hn xs hxs.1, ?_⟩
  · intro hσ
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact lt_of_lt_of_le ha (biInf_le (fun u => (f u : EReal)) (hxC n hn))
    · intro b hb
      rw [gt_iff_lt, iInf_lt_iff] at hb
      obtain ⟨u, hu⟩ := hb
      rw [iInf_lt_iff] at hu
      obtain ⟨huC, hub⟩ := hu
      obtain ⟨r, hur, hrb⟩ := EReal.lt_iff_exists_real_btwn.1 hub
      have hur' : f u < r := EReal.coe_lt_coe_iff.1 hur
      have hev := (hval hσ u huC).eventually (gt_mem_nhds hur')
      filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
      have := h20 n hn1 u huC
      calc (f (x n) : EReal) < (r : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
        _ < b := hrb
  · rintro hσ ⟨xs, hxsC, hxsmin⟩
    have hDanti : ∀ z ∈ C, (∀ v ∈ C, f z ≤ f v) → Antitone (fun n => bregman ψ z (x n)) := by
      intro z hz hzmin
      apply antitone_nat_of_succ_le
      intro n
      have h := hK n z hz
      have h1 := hzmin (x (n + 1)) (hxC _ (by omega))
      have hl := hlam (n + 1) (by omega)
      have := mul_nonneg hl.le (sub_nonneg.2 h1)
      linarith
    have hbdd : Bornology.IsBounded (Set.range x) := by
      apply (hψ.bounded_L₂ (bregman ψ xs (x 0)) xs (hCS hxsC)).subset
      rintro _ ⟨n, rfl⟩
      exact ⟨hxS n, hDanti xs hxsC hxsmin (Nat.zero_le n)⟩
    have hfx : ∀ ε > 0, ∀ᶠ n in atTop, f (x n) < f xs + ε := by
      intro ε hε
      have hev := (hval hσ xs hxsC).eventually (gt_mem_nhds (by linarith : f xs < f xs + ε))
      filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
      have := h20 n hn1 xs hxsC
      linarith
    obtain ⟨z, -, φ, hφ, hz⟩ := tendsto_subseq_of_bounded hbdd (fun n => Set.mem_range_self n)
    have hzle : extendTop C f z ≤ (f xs : EReal) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have h1' : f xs < r := EReal.coe_lt_coe_iff.1 h1
      have hev1 := hz.eventually (hlsc z (r : EReal) h2)
      have hev2 := hφ.tendsto_atTop.eventually (hfx (r - f xs) (by linarith))
      have hev3 := hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)
      obtain ⟨n, hn1, hn2, hn3⟩ := (hev1.and (hev2.and hev3)).exists
      have hC' := hxC _ hn3
      have hn1' : r < f (x (φ n)) := by
        have h := hn1
        simp only [Function.comp_apply, extendTop, if_pos hC'] at h
        exact_mod_cast h
      linarith
    have hzC : z ∈ C := by
      by_contra hzn
      have h := hzle
      simp [extendTop, hzn] at h
    have hzmin : ∀ v ∈ C, f z ≤ f v := by
      intro v hv
      have h := hzle
      simp only [extendTop, if_pos hzC] at h
      exact (EReal.coe_le_coe_iff.1 h).trans (hxsmin v hv)
    refine ⟨z, ⟨hzC, hzmin⟩, ?_⟩
    have hDz_sub : Tendsto (fun n => bregman ψ z (x (φ n))) atTop (𝓝 0) :=
      hψ.tendsto_zero (x ∘ φ) z (fun n => hxS _) hz
    have hDz : Tendsto (fun n => bregman ψ z (x n)) atTop (𝓝 0) := by
      have hA := hDanti z hzC hzmin
      have hlim := tendsto_atTop_ciInf hA ⟨0, by
        rintro _ ⟨n, rfl⟩
        exact hD z (hCS hzC) _ (hxS n)⟩
      have h0 : (⨅ n, bregman ψ z (x n)) = 0 :=
        tendsto_nhds_unique (hlim.comp hφ.tendsto_atTop) hDz_sub
      rwa [h0] at hlim
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨w, -, μ, hμ, hw⟩ :=
      tendsto_subseq_of_bounded hbdd (fun n => Set.mem_range_self (ns n))
    refine ⟨μ, ?_⟩
    have hwS : w ∈ closure S :=
      mem_closure_of_tendsto hw (Eventually.of_forall fun n => hxS _)
    have hcz : Tendsto (fun _ : ℕ => z) atTop (𝓝 w) :=
      hψ.tendsto_of_zero (fun _ => z) ((x ∘ ns) ∘ μ) w (fun _ => hCS hzC) (fun n => hxS _) hw
        hwS (by rw [Set.range_const]; exact Bornology.isBounded_singleton)
        (hDz.comp (hns.comp hμ.tendsto_atTop))
    have hzw : z = w := tendsto_nhds_unique tendsto_const_nhds hcz
    rw [hzw]
    exact hw
