-- Prove2me | solution 1 for ComonoNetPricing.DebtEquity.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:28:34.346473+00:00
-- url     : https://prove2.me/submissions/caf10aa8-c865-4ed3-b7f4-8bcda0bc5acb

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network
import Definitions.Def_ComonoNetPricing_DebtEquity_Model

namespace ComonoCore
open Matrix MeasureTheory ComonoNetPricing.DebtEquity

variable {n : ℕ} (N : Network n)

noncomputable def ub (x : Fin n → ℝ) : Fin n → ℝ := x + N.piMᵀ *ᵥ N.pbar - N.pbar

noncomputable def Ssum (V : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, N.piM j i * max (N.pbar j - max (-V j) 0) 0

variable {N}

lemma Ssum_nonneg (hN : N.Standing) (V : Fin n → ℝ) (i : Fin n) : 0 ≤ Ssum N V i :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hN.piM_nonneg j i) (le_max_right _ _))

lemma Ssum_le (hN : N.Standing) (V : Fin n → ℝ) (i : Fin n) :
    Ssum N V i ≤ (N.piMᵀ *ᵥ N.pbar) i := by
  unfold Ssum
  simp only [mulVec, dotProduct, transpose_apply]
  refine Finset.sum_le_sum (fun j _ => ?_)
  apply mul_le_mul_of_nonneg_left _ (hN.piM_nonneg j i)
  have := hN.pbar_pos j
  apply max_le _ this.le
  have : 0 ≤ max (-V j) 0 := le_max_right _ _
  linarith

lemma Ssum_mono (hN : N.Standing) {V W : Fin n → ℝ} (h : V ≤ W) (i : Fin n) :
    Ssum N V i ≤ Ssum N W i := by
  unfold Ssum
  refine Finset.sum_le_sum (fun j _ => ?_)
  apply mul_le_mul_of_nonneg_left _ (hN.piM_nonneg j i)
  have := h j
  apply max_le_max _ le_rfl
  have : max (-W j) 0 ≤ max (-V j) 0 := max_le_max (by linarith) le_rfl
  linarith

lemma Psi_apply (x V : Fin n → ℝ) (i : Fin n) :
    N.Psi x V i = if 0 ≤ V i then x i + Ssum N V i - N.pbar i
      else N.ax * x i + N.aL * Ssum N V i - N.pbar i := rfl

lemma Psi_ge (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) (V : Fin n → ℝ) :
    -N.pbar ≤ N.Psi x V := by
  intro i
  rw [Psi_apply]
  have h1 := Ssum_nonneg hN V i
  have h2 := hx i
  have h3 := hN.ax_mem.1
  have h4 := hN.aL_mem.1
  simp only [Pi.neg_apply, Pi.zero_apply] at *
  split_ifs
  · linarith
  · nlinarith

lemma Psi_le (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) (V : Fin n → ℝ) :
    N.Psi x V ≤ ub N x := by
  intro i
  rw [Psi_apply]
  have h1 := Ssum_nonneg hN V i
  have h1' := Ssum_le hN V i
  have h2 := hx i
  have h3 := hN.ax_mem.2
  have h4 := hN.aL_mem.2
  simp only [ub, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at *
  split_ifs
  · linarith
  · nlinarith

lemma Psi_mono (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) {V W : Fin n → ℝ} (h : V ≤ W) :
    N.Psi x V ≤ N.Psi x W := by
  intro i
  rw [Psi_apply, Psi_apply]
  have h0 := Ssum_mono hN h i
  have h1 := Ssum_nonneg hN V i
  have h2 := hx i
  have h3 := hN.ax_mem
  have h4 := hN.aL_mem
  have hi := h i
  simp only [Set.mem_Icc, Pi.zero_apply] at *
  split_ifs with ha hb hb
  · linarith
  · exact absurd (ha.trans hi) hb
  · nlinarith
  · nlinarith

lemma Psi_mono_x (hN : N.Standing) {x y : Fin n → ℝ} (hxy : x ≤ y) (V : Fin n → ℝ) :
    N.Psi x V ≤ N.Psi y V := by
  intro i
  rw [Psi_apply, Psi_apply]
  have := hxy i
  have h3 := hN.ax_mem.1
  split_ifs
  · linarith
  · nlinarith

/-- The greatest fixed point of `Ψ`, constructed à la Knaster–Tarski. -/
noncomputable def G (N : Network n) (x : Fin n → ℝ) : Fin n → ℝ :=
  sSup {V | V ∈ Set.Icc (-N.pbar) (ub N x) ∧ V ≤ N.Psi x V}

lemma G_spec (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) :
    N.Psi x (G N x) = G N x ∧ (∀ V, V ≤ N.Psi x V → V ≤ G N x) ∧ -N.pbar ≤ G N x := by
  set A := {V | V ∈ Set.Icc (-N.pbar) (ub N x) ∧ V ≤ N.Psi x V} with hA
  have hbdd : BddAbove A := ⟨ub N x, fun V hV => hV.1.2⟩
  have hmem : -N.pbar ∈ A :=
    ⟨⟨le_rfl, (Psi_ge hN hx _).trans (Psi_le hN hx (-N.pbar))⟩, Psi_ge hN hx _⟩
  have hne : A.Nonempty := ⟨_, hmem⟩
  have hle : ∀ V ∈ A, V ≤ G N x := fun V hV => le_csSup hbdd hV
  have h1 : G N x ≤ N.Psi x (G N x) := by
    apply csSup_le hne
    intro V hV
    exact hV.2.trans (Psi_mono hN hx (hle V hV))
  have h2 : N.Psi x (G N x) ∈ A :=
    ⟨⟨Psi_ge hN hx _, Psi_le hN hx _⟩, Psi_mono hN hx h1⟩
  have hfix : N.Psi x (G N x) = G N x := le_antisymm (hle _ h2) h1
  refine ⟨hfix, ?_, hle _ hmem⟩
  intro V hV
  have hV' : V ⊔ (-N.pbar) ∈ A := by
    have hp : V ⊔ (-N.pbar) ≤ N.Psi x (V ⊔ (-N.pbar)) :=
      sup_le (hV.trans (Psi_mono hN hx le_sup_left)) (Psi_ge hN hx _)
    exact ⟨⟨le_sup_right, hp.trans (Psi_le hN hx _)⟩, hp⟩
  exact le_sup_left.trans (hle _ hV')

lemma G_fixed_le (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) {V : Fin n → ℝ}
    (hV : N.Psi x V = V) : V ≤ G N x := (G_spec hN hx).2.1 V hV.ge

lemma Psi_eq_PsiStar (hN : N.Standing) (x : Fin n → ℝ) {V : Fin n → ℝ} (hV : -N.pbar ≤ V) :
    N.Psi x V = N.PsiStar x V := by
  funext i
  have hs : Ssum N V i = ∑ j, N.piM j i * (N.pbar j - max (-V j) 0) := by
    unfold Ssum
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    have := hV j
    have := hN.pbar_pos j
    simp only [Pi.neg_apply] at *
    apply max_eq_left
    have : max (-V j) 0 ≤ N.pbar j := max_le (by linarith) this.le
    linarith
  rw [Psi_apply, hs]
  unfold Network.PsiStar
  split_ifs <;> ring

lemma PsiStar_fixed_le_ub (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) {V : Fin n → ℝ}
    (hV : N.PsiStar x V = V) : V ≤ ub N x := by
  intro i
  rw [← hV]
  unfold Network.PsiStar
  have hT : ∑ j, N.piM j i * (N.pbar j - max (-V j) 0) ≤ (N.piMᵀ *ᵥ N.pbar) i := by
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_le_sum (fun j _ => ?_)
    apply mul_le_mul_of_nonneg_left _ (hN.piM_nonneg j i)
    have : 0 ≤ max (-V j) 0 := le_max_right _ _
    linarith
  have hU : 0 ≤ (N.piMᵀ *ᵥ N.pbar) i := by
    simp only [mulVec, dotProduct, transpose_apply]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hN.piM_nonneg j i) (hN.pbar_pos j).le)
  have h2 := hx i
  have h3 := hN.ax_mem
  have h4 := hN.aL_mem
  simp only [ub, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Set.mem_Icc] at *
  set T := ∑ j, N.piM j i * (N.pbar j - max (-V j) 0)
  split_ifs
  · linarith
  · rcases le_total 0 T with hT0 | hT0 <;> nlinarith

lemma PsiStar_fixed_post (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) {V : Fin n → ℝ}
    (hV : N.PsiStar x V = V) : V ≤ N.Psi x (V ⊔ (-N.pbar)) := by
  intro i
  by_cases hi : -N.pbar i ≤ V i
  · have hVi : (V ⊔ (-N.pbar)) i = V i := by
      simp only [Pi.sup_apply, Pi.neg_apply]; exact max_eq_left hi
    conv_lhs => rw [← hV]
    rw [Psi_apply, hVi]
    unfold Network.PsiStar
    have hT : ∑ j, N.piM j i * (N.pbar j - max (-V j) 0) ≤ Ssum N (V ⊔ (-N.pbar)) i := by
      unfold Ssum
      refine Finset.sum_le_sum (fun j _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hN.piM_nonneg j i)
      refine le_trans ?_ (le_max_left _ _)
      have : V j ≤ (V ⊔ (-N.pbar)) j := le_sup_left (a := V) (b := -N.pbar) j
      have : max (-(V ⊔ (-N.pbar)) j) 0 ≤ max (-V j) 0 := max_le_max (by linarith) le_rfl
      linarith
    have h4 := hN.aL_mem
    simp only [Set.mem_Icc] at h4
    split_ifs
    · linarith
    · nlinarith
  · replace hi := lt_of_not_ge hi
    have := Psi_ge hN hx (V ⊔ (-N.pbar)) i
    simp only [Pi.neg_apply] at this
    linarith

theorem G_isGreatest_PsiStar (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) :
    IsGreatest (Function.fixedPoints (N.PsiStar x)) (G N x) := by
  obtain ⟨hfix, hpost, hlb⟩ := G_spec hN hx
  refine ⟨?_, ?_⟩
  · show N.PsiStar x (G N x) = G N x
    rw [← Psi_eq_PsiStar hN x hlb]; exact hfix
  · intro V hV
    have hV : N.PsiStar x V = V := hV
    have hp : V ⊔ (-N.pbar) ≤ N.Psi x (V ⊔ (-N.pbar)) :=
      sup_le (PsiStar_fixed_post hN hx hV) (Psi_ge hN hx _)
    exact le_sup_left.trans (hpost _ hp)

theorem clearingWealth_eq_G (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) :
    N.clearingWealth x = G N x :=
  (G_isGreatest_PsiStar hN hx).csSup_eq

theorem G_mono (hN : N.Standing) {x y : Fin n → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    G N x ≤ G N y := by
  have hy : 0 ≤ y := hx.trans hxy
  obtain ⟨hfix, _, _⟩ := G_spec hN hx
  apply (G_spec hN hy).2.1
  calc G N x = N.Psi x (G N x) := hfix.symm
    _ ≤ N.Psi y (G N x) := Psi_mono_x hN hxy _


/-- The least fixed point of `Ψ`. -/
noncomputable def Lfp (N : Network n) (x : Fin n → ℝ) : Fin n → ℝ :=
  sInf {V | V ∈ Set.Icc (-N.pbar) (ub N x) ∧ N.Psi x V ≤ V}

lemma Lfp_spec (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) :
    N.Psi x (Lfp N x) = Lfp N x ∧ (∀ V, N.Psi x V = V → Lfp N x ≤ V) := by
  set A := {V | V ∈ Set.Icc (-N.pbar) (ub N x) ∧ N.Psi x V ≤ V} with hA
  have hbdd : BddBelow A := ⟨-N.pbar, fun V hV => hV.1.1⟩
  have hmem : ub N x ∈ A :=
    ⟨⟨(Psi_ge hN hx (ub N x)).trans (Psi_le hN hx _), le_rfl⟩, Psi_le hN hx _⟩
  have hne : A.Nonempty := ⟨_, hmem⟩
  have hle : ∀ V ∈ A, Lfp N x ≤ V := fun V hV => csInf_le hbdd hV
  have h1 : N.Psi x (Lfp N x) ≤ Lfp N x := by
    apply le_csInf hne
    intro V hV
    exact (Psi_mono hN hx (hle V hV)).trans hV.2
  have h2 : N.Psi x (Lfp N x) ∈ A :=
    ⟨⟨Psi_ge hN hx _, Psi_le hN hx _⟩, Psi_mono hN hx h1⟩
  have hfix : N.Psi x (Lfp N x) = Lfp N x := le_antisymm h1 (hle _ h2)
  refine ⟨hfix, ?_⟩
  intro V hV
  apply hle
  refine ⟨⟨?_, ?_⟩, hV.le⟩
  · rw [← hV]; exact Psi_ge hN hx _
  · rw [← hV]; exact Psi_le hN hx _

theorem propA1 (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∃ V, IsGreatest (Function.fixedPoints (N.Psi x)) V) ∧
      (∃ V, IsLeast (Function.fixedPoints (N.Psi x)) V) ∧
      ∀ V ∈ Function.fixedPoints (N.Psi x),
        V ∈ Set.Icc (-N.pbar) (x + N.piMᵀ *ᵥ N.pbar - N.pbar) := by
  refine ⟨⟨G N x, (G_spec hN hx).1, fun V hV => G_fixed_le hN hx hV⟩,
    ⟨Lfp N x, (Lfp_spec hN hx).1, fun V hV => (Lfp_spec hN hx).2 V hV⟩, ?_⟩
  intro V hV
  have hV : N.Psi x V = V := hV
  refine ⟨?_, ?_⟩
  · rw [← hV]; exact Psi_ge hN hx _
  · rw [← hV]; exact Psi_le hN hx _

theorem propA3 (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (W : Fin n → ℝ) (hW : IsGreatest (Function.fixedPoints (N.Psi x)) W) :
    N.PsiStar x W = W ∧ IsGreatest (Function.fixedPoints (N.PsiStar x)) W ∧
      N.clearingWealth x = W := by
  have hGW : G N x = W := by
    apply le_antisymm
    · exact hW.2 (G_spec hN hx).1
    · exact G_fixed_le hN hx hW.1
  subst hGW
  exact ⟨(G_isGreatest_PsiStar hN hx).1, G_isGreatest_PsiStar hN hx, clearingWealth_eq_G hN hx⟩

theorem propA6 (hN : N.Standing) (x y : Fin n → ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    N.clearingWealth x ≤ N.clearingWealth y ∧ N.payment x ≤ N.payment y ∧
      N.equity x ≤ N.equity y := by
  have h := G_mono hN hx hxy
  rw [← clearingWealth_eq_G hN hx, ← clearingWealth_eq_G hN (hx.trans hxy)] at h
  refine ⟨h, fun i => ?_, fun i => ?_⟩
  · unfold Network.payment
    have := h i
    have : max (-(N.clearingWealth y i)) 0 ≤ max (-(N.clearingWealth x i)) 0 :=
      max_le_max (by linarith) le_rfl
    linarith
  · unfold Network.equity
    exact max_le_max (h i) le_rfl

/-! ### Piecewise linearity -/

lemma one_sub_smul_dg (c : ℝ) (S : Finset (Fin n)) :
    (1 : Matrix (Fin n) (Fin n) ℝ) - c • Network.dg S =
      diagonal (fun i => 1 - c * if i ∈ S then 1 else 0) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Network.dg]
  · simp [Network.dg, Matrix.one_apply, hij]

lemma Mmat_apply (S : Finset (Fin n)) (i k : Fin n) :
    N.Mmat S i k = (if i = k then 1 else 0) -
      (1 - (1 - N.aL) * if i ∈ S then 1 else 0) * N.piM k i * (if k ∈ S then 1 else 0) := by
  simp only [Network.Mmat, one_sub_smul_dg]
  rw [Matrix.sub_apply, Matrix.one_apply]
  congr 1
  simp only [Network.dg, mul_diagonal, diagonal_mul, transpose_apply]

lemma Mmat_det_ne (hN : N.Standing) (S : Finset (Fin n)) : (N.Mmat S).det ≠ 0 := by
  apply det_ne_zero_of_sum_col_lt_diag
  intro k
  have hkk : ‖N.Mmat S k k‖ = 1 := by
    rw [Mmat_apply, if_pos rfl, hN.piM_diag k]; simp
  rw [hkk]
  have hL := hN.aL_mem
  simp only [Set.mem_Icc] at hL
  calc ∑ i ∈ Finset.univ.erase k, ‖N.Mmat S i k‖
      ≤ ∑ i ∈ Finset.univ.erase k, N.piM k i := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        rw [Mmat_apply, if_neg hik]
        have hp := hN.piM_nonneg k i
        split_ifs <;> simp [abs_of_nonneg, hp] <;>
          rw [abs_of_nonneg (by nlinarith)] <;> nlinarith
    _ ≤ ∑ i, N.piM k i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i _ _ => hN.piM_nonneg k i)
    _ < 1 := hN.row_sum_lt_one k

theorem piecewise (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    N.clearingWealth x =
      N.DeltaM (Finset.univ.filter (fun i => N.clearingWealth x i < 0)) *ᵥ x
        - N.deltaV (Finset.univ.filter (fun i => N.clearingWealth x i < 0)) := by
  set V := N.clearingWealth x with hVdef
  set S := Finset.univ.filter (fun i => V i < 0) with hS
  have hfix : N.PsiStar x V = V := by
    rw [hVdef, clearingWealth_eq_G hN hx]; exact (G_isGreatest_PsiStar hN hx).1
  set lam : Fin n → ℝ := fun i => if i ∈ S then 1 else 0 with hlam
  have hmemS : ∀ i, i ∈ S ↔ V i < 0 := fun i => by simp [hS]
  have hM : N.Mmat S *ᵥ V = (1 - (1 - N.ax) • Network.dg S) *ᵥ x
      - (1 - (1 - (1 - N.aL) • Network.dg S) * N.piMᵀ) *ᵥ N.pbar := by
    funext i
    have hfi := congrFun hfix i
    unfold Network.PsiStar at hfi
    have e1 : (N.Mmat S *ᵥ V) i = V i - (1 - (1 - N.aL) * lam i) *
        ∑ k, N.piM k i * (lam k * V k) := by
      have hk : ∀ k, N.Mmat S i k * V k = (if i = k then V k else 0) -
          (1 - (1 - N.aL) * lam i) * (N.piM k i * (lam k * V k)) := fun k => by
        rw [Mmat_apply]; simp only [hlam]; split_ifs <;> ring
      simp only [mulVec, dotProduct, hk, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, ← Finset.mul_sum]
    have e2 : ((1 - (1 - N.ax) • Network.dg S) *ᵥ x) i = (1 - (1 - N.ax) * lam i) * x i := by
      rw [one_sub_smul_dg, mulVec_diagonal]
    have e3 : ((1 - (1 - (1 - N.aL) • Network.dg S) * N.piMᵀ) *ᵥ N.pbar) i =
        N.pbar i - (1 - (1 - N.aL) * lam i) * ∑ k, N.piM k i * N.pbar k := by
      rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, one_sub_smul_dg, Pi.sub_apply,
        mulVec_diagonal]
      simp only [mulVec, dotProduct, transpose_apply, hlam]
    have e4 : ∑ j, N.piM j i * (N.pbar j - max (-V j) 0) =
        ∑ k, N.piM k i * N.pbar k + ∑ k, N.piM k i * (lam k * V k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have : max (-V k) 0 = -(lam k * V k) := by
        simp only [hlam, hmemS]
        split_ifs with h
        · rw [max_eq_left (by linarith)]; ring
        · rw [max_eq_right (by linarith)]; ring
      rw [this]; ring
    rw [e1, Pi.sub_apply, e2, e3]
    rw [e4] at hfi
    have hc1 : (if 0 ≤ V i then (1:ℝ) else N.ax) = 1 - (1 - N.ax) * lam i := by
      simp only [hlam, hmemS]; split_ifs with h1 h2 <;> first | (exfalso; linarith) | ring
    have hc2 : (if 0 ≤ V i then (1:ℝ) else N.aL) = 1 - (1 - N.aL) * lam i := by
      simp only [hlam, hmemS]; split_ifs with h1 h2 <;> first | (exfalso; linarith) | ring
    rw [hc1, hc2] at hfi
    linarith
  have hunit : IsUnit (N.Mmat S).det := isUnit_iff_ne_zero.mpr (Mmat_det_ne hN S)
  calc V = (N.Mmat S)⁻¹ *ᵥ (N.Mmat S *ᵥ V) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
    _ = _ := by
        rw [hM, mulVec_sub, mulVec_mulVec]
        rfl

end ComonoCore

open ComonoNetPricing.DebtEquity Matrix MeasureTheory

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∃ V, IsGreatest (Function.fixedPoints (N.Psi x)) V) ∧
      (∃ V, IsLeast (Function.fixedPoints (N.Psi x)) V) ∧
      ∀ V ∈ Function.fixedPoints (N.Psi x),
        V ∈ Set.Icc (-N.pbar) (x + N.piMᵀ *ᵥ N.pbar - N.pbar) := by
  exact ComonoCore.propA1 hN x hx
