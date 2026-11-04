-- Prove2me | solution 1 for FactorRMDP.ValueIter.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:40:26.654609+00:00
-- url     : https://prove2.me/submissions/30b1e039-6c47-4acb-a912-fbbbc85d3c98

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

set_option linter.unusedSectionVars false

namespace FactorRMDP.ValueIter.Sol51

open Matrix Filter Topology FactorRMDP.ValueIter

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {r : ℕ}

lemma dot_le_of_simplex {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) (y : S → ℝ) (c : ℝ)
    (hy : ∀ s, y s ≤ c) : w ⬝ᵥ y ≤ c := by
  have h1 : w ⬝ᵥ y ≤ ∑ s, w s * c :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hy s) (hw.1 s)
  rw [← Finset.sum_mul, hw.2, one_mul] at h1
  exact h1

lemma le_dot_of_simplex {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) (y : S → ℝ) (c : ℝ)
    (hy : ∀ s, c ≤ y s) : c ≤ w ⬝ᵥ y := by
  have h1 : ∑ s, w s * c ≤ w ⬝ᵥ y :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hy s) (hw.1 s)
  rw [← Finset.sum_mul, hw.2, one_mul] at h1
  exact h1

lemma abs_dot_le {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) (y : S → ℝ) : |w ⬝ᵥ y| ≤ ‖y‖ := by
  have hb : ∀ s, |y s| ≤ ‖y‖ := fun s => by
    have := norm_le_pi_norm y s
    rwa [Real.norm_eq_abs] at this
  rw [abs_le]
  constructor
  · exact le_dot_of_simplex hw y _ fun s => (abs_le.1 (hb s)).1
  · exact dot_le_of_simplex hw y _ fun s => (abs_le.1 (hb s)).2

lemma dot_const {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) (c : ℝ) :
    w ⬝ᵥ (fun _ => c) = c := by
  simp only [dotProduct]
  rw [← Finset.sum_mul, hw.2, one_mul]

namespace M'

variable (M : Model S A r)

lemma factorSet_simplex {i : Fin r} {w : S → ℝ} (hw : w ∈ M.factorSet i) :
    w ∈ stdSimplex ℝ S := by
  obtain ⟨W, hW, rfl⟩ := hw
  exact M.W_simplex W hW i

lemma factorSet_compact (i : Fin r) : IsCompact (M.factorSet i) :=
  M.W_compact.image (continuous_apply i)

lemma factorSet_nonempty (i : Fin r) : (M.factorSet i).Nonempty :=
  M.W_nonempty.image _

lemma img_compact (i : Fin r) (v : S → ℝ) :
    IsCompact ((fun w => w ⬝ᵥ v) '' M.factorSet i) :=
  ((M'.factorSet_compact M) i).image (Continuous.dotProduct continuous_id continuous_const)

lemma minFactor_spec (i : Fin r) (v : S → ℝ) :
    ∃ w ∈ M.factorSet i, w ⬝ᵥ v = M.minFactor i v :=
  ((M'.img_compact M) i v).sInf_mem (((M'.factorSet_nonempty M) i).image _)

lemma minFactor_le (i : Fin r) (v : S → ℝ) {w : S → ℝ} (hw : w ∈ M.factorSet i) :
    M.minFactor i v ≤ w ⬝ᵥ v :=
  csInf_le ((M'.img_compact M) i v).bddBelow ⟨w, hw, rfl⟩

lemma minFactor_lip (i : Fin r) (v v' : S → ℝ) :
    M.minFactor i v ≤ M.minFactor i v' + ‖v - v'‖ := by
  obtain ⟨w, hw, he⟩ := (M'.minFactor_spec M) i v'
  have h1 := (M'.minFactor_le M) i v hw
  have h2 := abs_dot_le ((M'.factorSet_simplex M) hw) (v - v')
  rw [dotProduct_sub] at h2
  have h3 := (abs_le.1 h2).2
  linarith

lemma minFactor_zero (i : Fin r) : M.minFactor i 0 = 0 := by
  unfold Model.minFactor
  have : (fun w : S → ℝ => w ⬝ᵥ (0 : S → ℝ)) '' M.factorSet i = {0} := by
    simp only [dotProduct_zero]
    exact ((M'.factorSet_nonempty M) i).image_const 0
  rw [this, csInf_singleton]

lemma F_le [Nonempty A] {lam : ℝ} (hlam : 0 ≤ lam) (v w : S → ℝ) (s : S) :
    M.F lam v s ≤ M.F lam w s + lam * ‖v - w‖ := by
  unfold Model.F
  apply Finset.sup'_le
  intro a _
  have hle := Finset.le_sup' (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i w)
    (Finset.mem_univ a)
  have h2 : ∑ i, M.u i s a * M.minFactor i v ≤ ∑ i, M.u i s a * M.minFactor i w + ‖v - w‖ := by
    calc ∑ i, M.u i s a * M.minFactor i v
        ≤ ∑ i, M.u i s a * (M.minFactor i w + ‖v - w‖) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((M'.minFactor_lip M) i v w) (M.u_nonneg i s a)
      _ = ∑ i, M.u i s a * M.minFactor i w + ‖v - w‖ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.u_sum, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h2 hlam
  nlinarith

lemma F_lip [Nonempty A] {lam : ℝ} (hlam : 0 ≤ lam) (v w : S → ℝ) :
    ‖M.F lam v - M.F lam w‖ ≤ lam * ‖v - w‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hlam (norm_nonneg _))]
  intro s
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_sub_le_iff]
  have h1 := (M'.F_le M) hlam v w s
  have h2 := (M'.F_le M) hlam w v s
  rw [norm_sub_rev w v] at h2
  constructor <;> linarith

lemma T_sum {π : S → A → ℝ} (hπ : π ∈ Policies S A) (s : S) : ∑ i, M.T π s i = 1 := by
  unfold Model.T
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.u_sum, mul_one]
  exact (hπ s).2

lemma T_nonneg {π : S → A → ℝ} (hπ : π ∈ Policies S A) (s : S) (i : Fin r) :
    0 ≤ M.T π s i :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (M.u_nonneg _ _ _)

lemma rpi_nonneg {π : S → A → ℝ} (hπ : π ∈ Policies S A) (s : S) : 0 ≤ M.rpi π s :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (M.rew_nonneg _ _)

lemma L_apply (π : S → A → ℝ) (W : Fin r → S → ℝ) (x : S → ℝ) (s : S) :
    (M.L π W *ᵥ x) s = ∑ i, M.T π s i * (W i ⬝ᵥ x) := by
  simp only [Model.L, ← mulVec_mulVec]
  rfl

lemma L_norm {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ} (hW : W ∈ M.Wset)
    (x : S → ℝ) : ‖M.L π W *ᵥ x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro s
  rw [(M'.L_apply M), Real.norm_eq_abs]
  calc |∑ i, M.T π s i * (W i ⬝ᵥ x)| ≤ ∑ i, |M.T π s i * (W i ⬝ᵥ x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, M.T π s i * ‖x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg ((M'.T_nonneg M) hπ s i)]
        exact mul_le_mul_of_nonneg_left (abs_dot_le (M.W_simplex W hW i) x) ((M'.T_nonneg M) hπ s i)
    _ = ‖x‖ := by rw [← Finset.sum_mul, (M'.T_sum M) hπ, one_mul]

lemma Lpow_norm {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ} (hW : W ∈ M.Wset)
    (x : S → ℝ) (t : ℕ) : ‖(M.L π W) ^ t *ᵥ x‖ ≤ ‖x‖ := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact ((M'.L_norm M) hπ hW _).trans ih

lemma summable_value {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    Summable (fun t : ℕ => lam ^ t • ((M.L π W) ^ t *ᵥ M.rpi π)) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hlam0 hlam1).mul_right ‖M.rpi π‖) fun t => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlam0 t)]
  exact mul_le_mul_of_nonneg_left ((M'.Lpow_norm M) hπ hW _ t) (pow_nonneg hlam0 t)

lemma bellman {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (s : S) :
    M.value lam π W s = M.rpi π s + lam * ∑ i, M.T π s i * (W i ⬝ᵥ M.value lam π W) := by
  have hsum := (M'.summable_value M) hπ hW hlam0 hlam1
  let Φ : (S → ℝ) →L[ℝ] (S → ℝ) :=
    LinearMap.toContinuousLinearMap (lam • Matrix.mulVecLin (M.L π W))
  have hΦ : ∀ y, Φ y = lam • (M.L π W *ᵥ y) := fun y => rfl
  have hvec : M.value lam π W = M.rpi π + lam • (M.L π W *ᵥ M.value lam π W) := by
    unfold Model.value
    conv_lhs => rw [hsum.tsum_eq_zero_add]
    simp only [pow_zero, one_smul, one_mulVec]
    congr 1
    have : ∀ t : ℕ, lam ^ (t + 1) • ((M.L π W) ^ (t + 1) *ᵥ M.rpi π)
        = Φ (lam ^ t • ((M.L π W) ^ t *ᵥ M.rpi π)) := by
      intro t
      rw [hΦ, mulVec_smul, smul_smul, pow_succ', pow_succ', ← mulVec_mulVec, mul_comm]
    rw [funext this, ← Φ.map_tsum hsum, hΦ]
  have := congrFun hvec s
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (M'.L_apply M)] at this
  exact this

lemma compare {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (y : S → ℝ)
    (hy : ∀ s, y s ≤ lam * ∑ i, M.T π s i * (W i ⬝ᵥ y)) : ∀ s, y s ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨s1, hs1⟩ := h
  have : Nonempty S := ⟨s1⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max y
  have h1 : ∀ i, W i ⬝ᵥ y ≤ y s0 := fun i => dot_le_of_simplex (M.W_simplex W hW i) y _ hs0
  have h2 : ∑ i, M.T π s0 i * (W i ⬝ᵥ y) ≤ y s0 := by
    calc ∑ i, M.T π s0 i * (W i ⬝ᵥ y) ≤ ∑ i, M.T π s0 i * y s0 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) ((M'.T_nonneg M) hπ s0 i)
      _ = y s0 := by rw [← Finset.sum_mul, (M'.T_sum M) hπ, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h2 hlam0
  have h4 := hy s0
  have h5 : 0 < y s0 := lt_of_lt_of_le hs1 (hs0 s1)
  nlinarith [mul_lt_mul_of_pos_right hlam1 h5]

lemma sum_sub_eq (π : S → A → ℝ) (W : Fin r → S → ℝ) (x y : S → ℝ) (s : S) :
    ∑ i, M.T π s i * (W i ⬝ᵥ (x - y)) =
      ∑ i, M.T π s i * (W i ⬝ᵥ x) - ∑ i, M.T π s i * (W i ⬝ᵥ y) := by
  simp only [dotProduct_sub, mul_sub, Finset.sum_sub_distrib]

lemma sub_sol {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (x : S → ℝ)
    (hx : ∀ s, x s ≤ M.rpi π s + lam * ∑ i, M.T π s i * (W i ⬝ᵥ x)) :
    ∀ s, x s ≤ M.value lam π W s := by
  have key := (M'.compare M) hπ hW hlam0 hlam1 (x - M.value lam π W) (fun s => by
    rw [(M'.sum_sub_eq M), Pi.sub_apply, mul_sub]
    have := (M'.bellman M) hπ hW hlam0 hlam1 s
    have := hx s
    linarith)
  intro s
  have := key s
  rw [Pi.sub_apply] at this
  linarith

lemma super_sol {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (x : S → ℝ)
    (hx : ∀ s, M.rpi π s + lam * ∑ i, M.T π s i * (W i ⬝ᵥ x) ≤ x s) :
    ∀ s, M.value lam π W s ≤ x s := by
  have key := (M'.compare M) hπ hW hlam0 hlam1 (M.value lam π W - x) (fun s => by
    rw [(M'.sum_sub_eq M), Pi.sub_apply, mul_sub]
    have := (M'.bellman M) hπ hW hlam0 hlam1 s
    have := hx s
    linarith)
  intro s
  have := key s
  rw [Pi.sub_apply] at this
  linarith

lemma p0_mono {x y : S → ℝ} (h : ∀ s, x s ≤ y s) : M.p0 ⬝ᵥ x ≤ M.p0 ⬝ᵥ y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (M.p0_mem.1 s)

lemma R_nonneg {π : S → A → ℝ} (hπ : π ∈ Policies S A) {W : Fin r → S → ℝ}
    (hW : W ∈ M.Wset) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    0 ≤ M.R lam π W := by
  have h := (M'.sub_sol M) hπ hW hlam0 hlam1 0 (fun s => by
    simp only [dotProduct_zero, mul_zero, Finset.sum_const_zero, add_zero, Pi.zero_apply]
    exact (M'.rpi_nonneg M) hπ s)
  have := (M'.p0_mono M) h
  rw [dotProduct_zero] at this
  exact this

lemma det_mem (d : S → A) : (fun s a => if a = d s then (1 : ℝ) else 0) ∈ Policies S A := by
  intro s
  refine ⟨fun a => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp

lemma rpi_det (d : S → A) (s : S) :
    M.rpi (fun s a => if a = d s then (1 : ℝ) else 0) s = M.rew s (d s) := by
  simp [Model.rpi]

lemma T_det (d : S → A) (s : S) (i : Fin r) :
    M.T (fun s a => if a = d s then (1 : ℝ) else 0) s i = M.u i s (d s) := by
  simp [Model.T]

end M'

end FactorRMDP.ValueIter.Sol51

open Matrix Filter Topology FactorRMDP.ValueIter FactorRMDP.ValueIter.Sol51

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    let v : ℕ → S → ℝ := fun k => M.viPI lam k
    let thr : ℝ → ℝ := fun ε => ε * (1 - lam) / (2 * lam)
    ∃ vstar : S → ℝ,
      M.F lam vstar = vstar ∧ (∀ w : S → ℝ, M.F lam w = w → w = vstar) ∧
      IsGreatest (M.z lam '' Policies S A) (M.p0 ⬝ᵥ vstar) ∧
      Tendsto v atTop (𝓝 vstar) ∧
      (∀ ε > 0, ∀ k : ℕ, ‖v (k + 1) - v k‖ < thr ε →
        ‖v (k + 1) - vstar‖ ≤ ε ∧
        ∀ d : S → A, (∀ s, v (k + 1) s =
            M.rew s (d s) + lam * ∑ i, M.u i s (d s) * M.minFactor i (v k)) →
          ∀ W ∈ M.Wset, M.p0 ⬝ᵥ vstar - ε ≤ M.R lam (fun s a => if a = d s then 1 else 0) W) ∧
      (∀ ε > 0, ∀ Rmax : ℝ, (∀ s a, M.rew s a ≤ Rmax) → ∀ k : ℕ, lam ^ k * Rmax < thr ε →
        ‖v (k + 1) - v k‖ < thr ε) := by
  intro v thr
  have hl0 : 0 ≤ lam := hlam0.le
  have hFlip := M'.F_lip M hl0
  have hK : ContractingWith (Real.toNNReal lam) (M.F lam) := by
    refine ⟨Real.toNNReal_lt_one.2 hlam1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hl0]; exact hFlip x y
  set vstar := ContractingWith.fixedPoint (M.F lam) hK with hvstar
  have hfix : M.F lam vstar = vstar := ContractingWith.fixedPoint_isFixedPt (f := M.F lam) hK
  have hv_succ : ∀ k, v (k + 1) = M.F lam (v k) := fun k =>
    Function.iterate_succ_apply' (M.F lam) k 0
  have hv0 : v 0 = 0 := rfl
  -- greedy deterministic policy for vstar
  have hex : ∀ s, ∃ a, M.F lam vstar s =
      M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i vstar := fun s => by
    obtain ⟨a, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i vstar)
    exact ⟨a, h⟩
  choose dstar hd using hex
  -- worst-case factor matrix for vstar
  choose Wst hWst using fun i => M'.minFactor_spec M i vstar
  have hWmem : Wst ∈ M.Wset := by
    rw [hR]; exact fun i _ => (hWst i).1
  have hUB : ∀ π ∈ Policies S A, M.z lam π ≤ M.p0 ⬝ᵥ vstar := by
    intro π hπ
    have hsup : ∀ s, M.rpi π s + lam * ∑ i, M.T π s i * (Wst i ⬝ᵥ vstar) ≤ vstar s := by
      intro s
      simp_rw [(hWst _).2]
      have heq : M.rpi π s + lam * ∑ i, M.T π s i * M.minFactor i vstar =
          ∑ a, π s a * (M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i vstar) := by
        simp only [Model.rpi, Model.T, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
      rw [heq]
      calc ∑ a, π s a * (M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i vstar)
          ≤ ∑ a, π s a * M.F lam vstar s := by
            refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((hπ s).1 a)
            exact Finset.le_sup' (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i vstar)
              (Finset.mem_univ a)
        _ = vstar s := by rw [← Finset.sum_mul, (hπ s).2, one_mul, hfix]
    have hV := M'.super_sol M hπ hWmem hl0 hlam1 vstar hsup
    have hbdd : BddBelow (M.evalValues lam π) :=
      ⟨0, by rintro _ ⟨W, hW, rfl⟩; exact M'.R_nonneg M hπ hW hl0 hlam1⟩
    calc M.z lam π ≤ M.R lam π Wst := csInf_le hbdd ⟨Wst, hWmem, rfl⟩
      _ ≤ M.p0 ⬝ᵥ vstar := M'.p0_mono M hV
  have hLB : M.p0 ⬝ᵥ vstar ≤ M.z lam (fun s a => if a = dstar s then (1 : ℝ) else 0) := by
    apply le_csInf (M.W_nonempty.image _)
    rintro _ ⟨W, hW, rfl⟩
    apply M'.p0_mono M
    apply M'.sub_sol M (M'.det_mem dstar) hW hl0 hlam1
    intro s
    rw [M'.rpi_det]
    simp_rw [M'.T_det]
    conv_lhs => rw [← hfix, hd s]
    have : ∑ i, M.u i s (dstar s) * M.minFactor i vstar ≤
        ∑ i, M.u i s (dstar s) * (W i ⬝ᵥ vstar) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (M'.minFactor_le M i vstar ⟨W, hW, rfl⟩) (M.u_nonneg _ _ _)
    have := mul_le_mul_of_nonneg_left this hl0
    linarith
  refine ⟨vstar, hfix, fun w hw => ContractingWith.fixedPoint_unique hK hw, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨_, M'.det_mem dstar, le_antisymm (hUB _ (M'.det_mem dstar)) hLB⟩, ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    exact hUB π hπ
  · exact hK.tendsto_iterate_fixedPoint 0
  · intro ε hε k hk
    set η := ‖v (k + 1) - v k‖ with hη
    have hdist : ‖v (k + 1) - vstar‖ * (1 - lam) ≤ lam * η := by
      have h1 : ‖v (k + 1) - vstar‖ ≤ lam * ‖v k - vstar‖ := by
        rw [hv_succ]
        conv_lhs => rw [← hfix]
        exact hFlip _ _
      have h2 : ‖v k - vstar‖ ≤ ‖v k - v (k + 1)‖ + ‖v (k + 1) - vstar‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [norm_sub_rev (v k) (v (k + 1))] at h2
      nlinarith
    set c := lam * η / (1 - lam) with hc
    have h1l : 0 < 1 - lam := by linarith
    have hceq : c * (1 - lam) = lam * η := by
      rw [hc]; field_simp
    have hD : ‖v (k + 1) - vstar‖ ≤ c := by
      rw [hc, le_div_iff₀ h1l]; exact hdist
    have hthr : lam * thr ε = ε * (1 - lam) / 2 := by
      show lam * (ε * (1 - lam) / (2 * lam)) = _
      field_simp
    have hc2 : c < ε / 2 := by
      have := mul_lt_mul_of_pos_left hk hlam0
      rw [hthr] at this
      rw [hc, div_lt_iff₀ h1l]
      linarith
    refine ⟨by linarith, ?_⟩
    intro d hdk W hW
    let x : S → ℝ := v (k + 1) - fun _ => c
    have hη0 : 0 ≤ η := norm_nonneg _
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hWx : ∀ i, M.minFactor i (v k) - (η + c) ≤ W i ⬝ᵥ x := by
      intro i
      have hs := M.W_simplex W hW i
      have e1 : W i ⬝ᵥ x = W i ⬝ᵥ v k + W i ⬝ᵥ (v (k + 1) - v k) - c := by
        simp only [x, dotProduct_sub, dot_const hs]; ring
      have e2 := (abs_le.1 (abs_dot_le hs (v (k + 1) - v k))).1
      have e3 := M'.minFactor_le M i (v k) ⟨W, hW, rfl⟩
      rw [e1]
      linarith
    have hsub := M'.sub_sol M (M'.det_mem d) hW hl0 hlam1 x (fun s => by
      rw [M'.rpi_det]
      simp_rw [M'.T_det]
      have hs1 : ∑ i, M.u i s (d s) * (M.minFactor i (v k) - (η + c)) ≤
          ∑ i, M.u i s (d s) * (W i ⬝ᵥ x) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hWx i) (M.u_nonneg _ _ _)
      have e : ∑ i, M.u i s (d s) * (M.minFactor i (v k) - (η + c)) =
          ∑ i, M.u i s (d s) * M.minFactor i (v k) - (η + c) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, M.u_sum, one_mul]
      rw [e] at hs1
      have hs2 := mul_le_mul_of_nonneg_left hs1 hl0
      have hxs : x s = v (k + 1) s - c := rfl
      rw [hxs, hdk s]
      nlinarith)
    have hR1 := M'.p0_mono M hsub
    have hpx : M.p0 ⬝ᵥ x = M.p0 ⬝ᵥ v (k + 1) - c := by
      simp only [x, dotProduct_sub, dot_const M.p0_mem]
    have hp2 := (abs_le.1 (abs_dot_le M.p0_mem (v (k + 1) - vstar))).1
    rw [dotProduct_sub] at hp2
    show M.p0 ⬝ᵥ vstar - ε ≤ M.p0 ⬝ᵥ M.value lam _ W
    linarith
  · intro ε hε Rmax hRmax k hk
    have hthrpos : 0 < thr ε := div_pos (mul_pos hε (by linarith)) (by linarith)
    rcases isEmpty_or_nonempty S with hS | ⟨⟨s0⟩⟩
    · have : v (k + 1) - v k = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]; exact hthrpos
    · have hRm : 0 ≤ Rmax := le_trans (M.rew_nonneg s0 (Classical.arbitrary A)) (hRmax _ _)
      have hgeo : ∀ k, ‖v (k + 1) - v k‖ ≤ lam ^ k * ‖v 1 - v 0‖ := by
        intro k
        induction k with
        | zero => simp
        | succ n ih =>
          rw [hv_succ (n + 1), hv_succ n]
          calc ‖M.F lam (M.F lam (v n)) - M.F lam (v n)‖ ≤ lam * ‖M.F lam (v n) - v n‖ :=
                hFlip _ _
            _ ≤ lam * (lam ^ n * ‖v 1 - v 0‖) := by
                rw [← hv_succ n]; exact mul_le_mul_of_nonneg_left ih hl0
            _ = lam ^ (n + 1) * ‖v 1 - v 0‖ := by ring
      have h1 : ‖v 1 - v 0‖ ≤ Rmax := by
        rw [hv_succ 0, hv0, sub_zero, pi_norm_le_iff_of_nonneg hRm]
        intro s
        rw [Real.norm_eq_abs, abs_le]
        have a0 := Classical.arbitrary A
        constructor
        · have h0 : M.rew s a0 ≤ M.F lam 0 s := by
            have := Finset.le_sup' (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i 0)
              (Finset.mem_univ a0)
            unfold Model.F
            simp only [M'.minFactor_zero, mul_zero, Finset.sum_const_zero, add_zero] at this ⊢
            exact this
          linarith [M.rew_nonneg s a0]
        · unfold Model.F
          apply Finset.sup'_le
          intro a _
          simpa [M'.minFactor_zero] using hRmax s a
      calc ‖v (k + 1) - v k‖ ≤ lam ^ k * ‖v 1 - v 0‖ := hgeo k
        _ ≤ lam ^ k * Rmax := mul_le_mul_of_nonneg_left h1 (pow_nonneg hl0 k)
        _ < thr ε := hk
