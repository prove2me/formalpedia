-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.zero_row_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:26.173623+00:00
-- url     : https://prove2.me/submissions/6d4c75d2-5d2c-483e-9657-3f4d55c701dc

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Theorems.Thm_FiniteSampleDependence_Rigidity_coordinate_transfers_unused_state

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Zero

open FiniteSampleDependence.Rigidity Matrix

lemma rank_ne_zero_of_ne_zero {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (h : A ≠ 0) :
    A.rank ≠ 0 := by
  intro h0
  apply h
  unfold Matrix.rank at h0
  have := Submodule.finrank_eq_zero.mp h0
  ext i j
  have h1 : A.mulVecLin (Pi.single j 1) = 0 := by
    have hm : A.mulVecLin (Pi.single j 1) ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
    rw [this] at hm
    simpa using hm
  have := congrFun h1 i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

lemma rank_one_of_single_row {n m : ℕ} (p : Fin n) (V : Matrix (Fin n) (Fin m) ℝ)
    (hV : V ∈ simplex n m) (hrow : ∀ i, i ≠ p → ∀ α, V i α = 0) : V.rank = 1 := by
  have hV' : V = Matrix.vecMulVec (Pi.single p 1) (V p) := by
    ext i α
    by_cases h : i = p
    · subst h; simp [Matrix.vecMulVec_apply]
    · simp [Matrix.vecMulVec_apply, h, hrow i h α]
  apply le_antisymm
  · rw [hV']; exact Matrix.rank_vecMulVec_le _ _
  · apply Nat.one_le_iff_ne_zero.mpr
    apply rank_ne_zero_of_ne_zero
    intro h0
    have h1 := hV.2
    rw [h0] at h1
    simp [tau] at h1

/-- The direction `D`. -/
noncomputable def Dir {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (J : Finset (Fin n)) :
    Ambient n m :=
  ∑ j ∈ J, ∑ β, U j β • (entryDir p β - entryDir j β)

lemma Dir_apply {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (J : Finset (Fin n))
    (i : Fin n) (α : Fin m) :
    Dir U p J i α = (if i = p then ∑ j ∈ J, U j α else 0) - (if i ∈ J then U i α else 0) := by
  have e : ∀ (q : Fin n) (β : Fin m),
      entryDir q β i α = if i = q then (if α = β then 1 else 0) else 0 := by
    intro q β
    by_cases h : i = q
    · subst h; simp [entryDir, Pi.single_apply]
    · simp [entryDir, Pi.single_apply, h]
  simp only [Dir, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : i = p
    · simp [h]
    · simp [h]
  · by_cases h : i ∈ J
    · simp [h, Finset.sum_ite_eq]
    · simp [h]

lemma sum_Dir {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (J : Finset (Fin n))
    (hp : p ∉ J) (α : Fin m) : ∑ i, Dir U p J i α = 0 := by
  simp only [Dir_apply, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', Finset.sum_ite_mem]

lemma pos_case {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F) (hIZ : IZ F)
    (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ) (hG : IsC1Extension F Ω G)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (r : Fin n) (hr : ∀ α, U r α = 0)
    (hpos : ∀ i α, i ≠ r → 0 < U i α) : F U = 0 := by
  obtain ⟨p, hpr⟩ : ∃ p : Fin n, p ≠ r := by
    by_contra h
    push_neg at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    rw [← h1] at h0
    simp [Fin.ext_iff] at h0
  set J : Finset (Fin n) := (Finset.univ.erase p).erase r with hJ
  have hmemJ : ∀ i, i ∈ J ↔ i ≠ r ∧ i ≠ p := by
    intro i; simp [hJ]
  have hpJ : p ∉ J := by simp [hmemJ]
  have hrJ : r ∉ J := by simp [hmemJ]
  set D : Ambient n m := Dir U p J with hD
  let M : ℝ → Matrix (Fin n) (Fin m) ℝ := fun s => Matrix.of (fun i α => U i α + s * D i α)
  have hMsymm : ∀ s, Matrix.of.symm (M s) = Matrix.of.symm U + s • D := by
    intro s; ext i α; simp [M]
  have hM : ∀ s i α, M s i α = U i α + s * ((if i = p then ∑ j ∈ J, U j α else 0)
      - (if i ∈ J then U i α else 0)) := by
    intro s i α; simp [M, hD, Dir_apply]
  have hMr : ∀ s α, M s r α = 0 := by
    intro s α; rw [hM]; simp [hr, hpr.symm, hrJ]
  have hMp : ∀ s, 0 ≤ s → ∀ α, 0 < M s p α := by
    intro s hs α
    rw [hM]
    simp only [if_true, hpJ, if_false, sub_zero]
    have := hpos p α hpr
    have : 0 ≤ ∑ j ∈ J, U j α := Finset.sum_nonneg fun j _ => (hU.1 j α)
    positivity
  have hMj : ∀ s, s ≤ 1 → ∀ i α, i ∈ J → M s i α = (1 - s) * U i α := by
    intro s hs i α hi
    have hip : i ≠ p := ((hmemJ i).1 hi).2
    rw [hM]
    simp [hip, hi]; ring
  have hMpos : ∀ s, 0 ≤ s → s < 1 → ∀ i α, i ≠ r → 0 < M s i α := by
    intro s hs0 hs1 i α hi
    by_cases hip : i = p
    · subst hip; exact hMp s hs0 α
    · rw [hMj s hs1.le i α ((hmemJ i).2 ⟨hi, hip⟩)]
      exact mul_pos (by linarith) (hpos i α hi)
  have hMsimp : ∀ s, 0 ≤ s → s ≤ 1 → M s ∈ simplex n m := by
    intro s hs0 hs1
    refine ⟨fun i α => ?_, ?_⟩
    · by_cases hir : i = r
      · subst hir; rw [hMr]
      · by_cases hip : i = p
        · subst hip; exact (hMp s hs0 α).le
        · rw [hMj s hs1 i α ((hmemJ i).2 ⟨hir, hip⟩)]
          exact mul_nonneg (by linarith) (hU.1 i α)
    · have h1 := hU.2
      unfold tau at h1 ⊢
      have : ∀ i α, M s i α = U i α + s * D i α := fun i α => by simp [M]
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm (f := fun i α => D i α)]
      simp [hD, sum_Dir U p J hpJ, h1]
  -- the path
  let g : ℝ → ℝ := fun s => G (Matrix.of.symm U + s • D)
  have hGcont : ContinuousOn G Ω := hG.2.2.1.continuousOn
  have hmaps : ∀ s ∈ Set.Icc (0 : ℝ) 1, Matrix.of.symm U + s • D ∈ Ω := by
    intro s hs
    have := hG.2.1 _ (hMsimp s hs.1 hs.2)
    rwa [hMsymm] at this
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    apply hGcont.comp (by fun_prop) hmaps
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt g 0 (Set.Ici s) s := by
    intro s hs
    have hmem := hmaps s ⟨hs.1, hs.2.le⟩
    have hdiff : DifferentiableAt ℝ G (Matrix.of.symm U + s • D) :=
      (hG.2.2.1.differentiableOn one_ne_zero).differentiableAt (hG.1.mem_nhds hmem)
    have hd1 : HasDerivAt (fun s : ℝ => Matrix.of.symm U + s • D) D s := by
      simpa using ((hasDerivAt_id s).smul_const D).const_add (Matrix.of.symm U)
    have hd2 := hdiff.hasFDerivAt.comp_hasDerivAt s hd1
    have hzero : fderiv ℝ G (Matrix.of.symm U + s • D) D = 0 := by
      have key : ∀ x : Ambient n m,
          (∀ j ∈ J, ∀ β, fderiv ℝ G x (entryDir p β) = fderiv ℝ G x (entryDir j β)) →
          fderiv ℝ G x (Dir U p J) = 0 := by
        intro x hx
        rw [Dir, map_sum]
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun β _ => ?_
        rw [map_smul, map_sub, hx j hj β]; simp
      apply key
      intro j hj β
      have hjr : j ≠ r := ((hmemJ j).1 hj).1
      have hjp : j ≠ p := ((hmemJ j).1 hj).2
      have := coordinate_transfers_unused_state hn hm F hF (M s) (hMsimp s hs.1 hs.2.le) r
        (hMr s) (hMpos s hs.1 hs.2) Ω G hG p j hpr hjr hjp.symm β
      rwa [hMsymm] at this
    rw [hzero] at hd2
    exact hd2.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv 1 ⟨zero_le_one, le_rfl⟩
  have hg0 : g 0 = F U := by
    have := hG.2.2.2 U hU
    simpa [g] using this
  have hg1 : g 1 = F (M 1) := by
    have := hG.2.2.2 (M 1) (hMsimp 1 zero_le_one le_rfl)
    rw [hMsymm] at this
    simpa [g] using this
  have hrank : (M 1).rank = 1 := by
    apply rank_one_of_single_row p _ (hMsimp 1 zero_le_one le_rfl)
    intro i hip α
    by_cases hir : i = r
    · subst hir; exact hMr 1 α
    · rw [hMj 1 le_rfl i α ((hmemJ i).2 ⟨hir, hip⟩)]; simp
  have := hIZ _ (hMsimp 1 zero_le_one le_rfl) hrank
  rw [← hg0, ← hconst, hg1, this]

lemma general_case {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F) (hIZ : IZ F)
    (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ) (hG : IsC1Extension F Ω G)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (r : Fin n) (hr : ∀ α, U r α = 0) :
    F U = 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set c : ℝ := 1 / ((m : ℝ) * ((n : ℝ) - 1)) with hc
  have hcpos : 0 < c := by positivity
  let B : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i α => if i = r then 0 else c
  have hB : B ∈ simplex n m := by
    refine ⟨fun i α => ?_, ?_⟩
    · simp only [B, Matrix.of_apply]; split_ifs <;> linarith
    · unfold tau
      have h1 : ∀ i : Fin n, ∑ α : Fin m, B i α = if i = r then 0 else (m : ℝ) * c := by
        intro i; by_cases h : i = r <;> simp [B, h]
      simp only [h1]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      simp only [if_true]
      rw [Finset.sum_congr rfl (g := fun _ => (m : ℝ) * c)
        (fun i hi => by simp [(Finset.ne_of_mem_erase hi)])]
      simp [Finset.card_erase_of_mem, hc]
      rw [Nat.cast_sub (by omega)]; push_cast; field_simp
  let V : ℝ → Matrix (Fin n) (Fin m) ℝ := fun ε => (1 - ε) • U + ε • B
  have hVsymm : ∀ ε, Matrix.of.symm (V ε) =
      (1 - ε) • Matrix.of.symm U + ε • Matrix.of.symm B := by
    intro ε; ext i α; simp [V]
  have hVsimp : ∀ ε, 0 ≤ ε → ε ≤ 1 → V ε ∈ simplex n m := by
    intro ε h0 h1
    refine ⟨fun i α => ?_, ?_⟩
    · simp only [V, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg (by linarith) (hU.1 i α)) (mul_nonneg h0 (hB.1 i α))
    · have := hU.2
      have h2 := hB.2
      unfold tau at this h2 ⊢
      simp only [V, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, this, h2]
      ring
  have hVzero : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, F (V ε) = 0 := by
    intro ε hε
    refine pos_case hn hm F hF hIZ Ω G hG (V ε) (hVsimp ε hε.1.le hε.2.le) r ?_ ?_
    · intro α; simp [V, hr, B]
    · intro i α hi
      simp only [V, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, B, Matrix.of_apply, hi,
        if_false]
      have := hU.1 i α
      have h1 : 0 < 1 - ε := by linarith [hε.2]
      have := hε.1
      positivity
  have hGc : ContinuousAt G (Matrix.of.symm U) := by
    have hmem := hG.2.1 U hU
    exact hG.2.2.1.continuousOn.continuousAt (hG.1.mem_nhds hmem)
  have hpath : Filter.Tendsto
      (fun ε : ℝ => (1 - ε) • Matrix.of.symm U + ε • Matrix.of.symm B) (nhds 0)
      (nhds (Matrix.of.symm U)) := by
    have : Continuous (fun ε : ℝ => (1 - ε) • Matrix.of.symm U + ε • Matrix.of.symm B) := by
      fun_prop
    simpa using this.tendsto 0
  have h1 : Filter.Tendsto
      (fun ε : ℝ => G ((1 - ε) • Matrix.of.symm U + ε • Matrix.of.symm B))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (G (Matrix.of.symm U))) :=
    (hGc.tendsto.comp hpath).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto
      (fun ε : ℝ => G ((1 - ε) • Matrix.of.symm U + ε • Matrix.of.symm B))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    rw [← hVsymm, hG.2.2.2 _ (hVsimp ε hε.1.le hε.2.le), hVzero ε hε]
  have := tendsto_nhds_unique h1 h2
  rw [← hG.2.2.2 U hU]
  exact this


end FiniteSampleDependence.Dev.Zero

namespace FiniteSampleDependence.Rigidity

open FiniteSampleDependence.Dev.Zero

theorem chk_zero_row_vanishing {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hC1 : IsC1Extendable F) (hF : LFDPI F) (hIZ : IZ F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (hzero : ∃ r, ∀ α, U r α = 0) :
    F U = 0 := by
  obtain ⟨Ω, G, hG⟩ := hC1
  obtain ⟨r, hr⟩ := hzero
  exact general_case hn hm F hF hIZ Ω G hG U hU r hr

end FiniteSampleDependence.Rigidity
end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_zero_row_vanishing := @FiniteSampleDependence.Rigidity.chk_zero_row_vanishing
