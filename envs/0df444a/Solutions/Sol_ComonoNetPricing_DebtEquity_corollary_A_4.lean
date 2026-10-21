-- Prove2me | solution 1 for ComonoNetPricing.DebtEquity.corollary_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:38:56.934718+00:00
-- url     : https://prove2.me/submissions/b4db943e-0cf5-4d78-a523-0cc8d935088f

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


/-! ### Right-continuity of the greatest clearing wealth along decreasing endowments -/

open Filter Topology

lemma Ssum_continuous (i : Fin n) : Continuous (fun V : Fin n → ℝ => Ssum N V i) := by
  unfold Ssum
  fun_prop

theorem G_limit_fixed (hN : N.Standing) {x : Fin n → ℝ} (xs : ℕ → Fin n → ℝ)
    (hxs0 : ∀ m, 0 ≤ xs m) (hxs : Tendsto xs atTop (𝓝 x)) (W : Fin n → ℝ)
    (hW : Tendsto (fun m => G N (xs m)) atTop (𝓝 W)) (hWle : ∀ m, W ≤ G N (xs m)) :
    N.Psi x W = W := by
  funext i
  have hfix : ∀ m, N.Psi (xs m) (G N (xs m)) i = G N (xs m) i :=
    fun m => congrFun (G_spec hN (hxs0 m)).1 i
  have hWi : Tendsto (fun m => G N (xs m) i) atTop (𝓝 (W i)) := tendsto_pi_nhds.1 hW i
  have hxi : Tendsto (fun m => xs m i) atTop (𝓝 (x i)) := tendsto_pi_nhds.1 hxs i
  have hS : Tendsto (fun m => Ssum N (G N (xs m)) i) atTop (𝓝 (Ssum N W i)) :=
    ((Ssum_continuous i).tendsto W).comp hW
  rw [Psi_apply]
  split_ifs with h0
  · have hlim : Tendsto (fun m => xs m i + Ssum N (G N (xs m)) i - N.pbar i) atTop
        (𝓝 (x i + Ssum N W i - N.pbar i)) := (hxi.add hS).sub_const _
    have heq : ∀ m, xs m i + Ssum N (G N (xs m)) i - N.pbar i = G N (xs m) i := by
      intro m
      have := hfix m
      rw [Psi_apply, if_pos (h0.trans (hWle m i))] at this
      exact this
    simp only [heq] at hlim
    exact tendsto_nhds_unique hlim hWi
  · push Not at h0
    have hlim : Tendsto (fun m => N.ax * xs m i + N.aL * Ssum N (G N (xs m)) i - N.pbar i)
        atTop (𝓝 (N.ax * x i + N.aL * Ssum N W i - N.pbar i)) :=
      ((hxi.const_mul _).add (hS.const_mul _)).sub_const _
    have hev : ∀ᶠ m in atTop, N.ax * xs m i + N.aL * Ssum N (G N (xs m)) i - N.pbar i
        = G N (xs m) i := by
      filter_upwards [hWi.eventually_lt_const h0] with m hm
      have := hfix m
      rw [Psi_apply, if_neg (not_le.mpr hm)] at this
      exact this
    exact tendsto_nhds_unique (hlim.congr' hev) hWi

theorem rc_nonneg (hN : N.Standing) (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s) (s : ℝ) (hs : 0 ≤ s)
    (i : Fin n) (h : ∀ t, s < t → 0 ≤ G N (f t) i) : 0 ≤ G N (f s) i := by
  set ts : ℕ → ℝ := fun m => s + 1 / ((m : ℝ) + 1) with hts
  have hts_gt : ∀ m, s < ts m := fun m => by
    simp only [hts]; have : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
    linarith
  have hts_anti : Antitone ts := by
    intro a b hab
    simp only [hts]
    have : (1:ℝ) / ((b:ℝ) + 1) ≤ 1 / ((a:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hts_lim : Tendsto ts atTop (𝓝[Set.Ici s] s) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall (fun m => (hts_gt m).le)⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add s
    simpa [hts] using this
  set xs : ℕ → Fin n → ℝ := fun m => f (ts m) with hxs
  have hxs0 : ∀ m, 0 ≤ xs m := fun m => hf_nonneg _ (hs.trans (hts_gt m).le)
  have hxs_lim : Tendsto xs atTop (𝓝 (f s)) := (hf_rc s hs).tendsto.comp hts_lim
  have hG_anti : ∀ a b, a ≤ b → G N (xs b) ≤ G N (xs a) := by
    intro a b hab
    apply G_mono hN (hxs0 b)
    exact hf_mono (Set.mem_Ici.2 (hs.trans (hts_gt b).le)) (Set.mem_Ici.2 (hs.trans (hts_gt a).le))
      (hts_anti hab)
  have hbdd : ∀ j, BddBelow (Set.range (fun m => G N (xs m) j)) := fun j =>
    ⟨-N.pbar j, by rintro _ ⟨m, rfl⟩; exact (G_spec hN (hxs0 m)).2.2 j⟩
  set W : Fin n → ℝ := fun j => ⨅ m, G N (xs m) j with hW
  have hWlim : Tendsto (fun m => G N (xs m)) atTop (𝓝 W) := by
    apply tendsto_pi_nhds.2
    intro j
    exact tendsto_atTop_ciInf (fun a b hab => hG_anti a b hab j) (hbdd j)
  have hWle : ∀ m, W ≤ G N (xs m) := fun m j => ciInf_le (hbdd j) m
  have hfixW := G_limit_fixed hN xs hxs0 hxs_lim W hWlim hWle
  have hWG : W ≤ G N (f s) := G_fixed_le hN (hf_nonneg s hs) hfixW
  have hWi : 0 ≤ W i := le_ciInf (fun m => h _ (hts_gt m))
  exact hWi.trans (hWG i)

theorem threshold (hN : N.Standing) (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s) (s : ℝ) (hs : 0 ≤ s)
    (i : Fin n) : N.clearingWealth (f s) i < 0 ↔ ENNReal.ofReal s < N.qstar f i := by
  constructor
  · intro hneg
    by_contra hq
    push Not at hq
    apply absurd hneg
    apply not_lt.2
    rw [clearingWealth_eq_G hN (hf_nonneg s hs)]
    apply rc_nonneg hN f hf_mono hf_nonneg hf_rc s hs i
    intro t hst
    have ht : 0 ≤ t := hs.trans hst.le
    have hlt : N.qstar f i < ENNReal.ofReal t :=
      hq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hs.trans_lt hst)).2 hst)
    unfold Network.qstar at hlt
    obtain ⟨b, ⟨s', ⟨hs'0, hs'⟩, rfl⟩, hb⟩ := sInf_lt_iff.1 hlt
    have hs't : s' < t := (ENNReal.ofReal_lt_ofReal_iff'.1 hb).1
    rw [clearingWealth_eq_G hN (hf_nonneg s' hs'0)] at hs'
    have := G_mono hN (hf_nonneg s' hs'0)
      (hf_mono (Set.mem_Ici.2 hs'0) (Set.mem_Ici.2 ht) hs't.le)
    exact hs'.trans (this i)
  · intro hlt
    by_contra hnn
    push Not at hnn
    apply absurd hlt
    apply not_lt.2
    exact sInf_le ⟨s, ⟨hs, hnn⟩, rfl⟩


/-! ### The partition of the factor space -/

lemma qExt_succ_le (f : ℝ → Fin n → ℝ) (hord : Antitone (N.qstar f)) (k : ℕ) :
    N.qExt f (k + 1) ≤ N.qExt f k := by
  unfold Network.qExt
  by_cases hk : k = 0
  · simp [hk]
  · rw [dif_neg (Nat.succ_ne_zero k), dif_neg hk]
    by_cases hkn : k + 1 ≤ n
    · rw [dif_pos hkn, dif_pos (by omega)]
      apply hord
      show k - 1 ≤ k + 1 - 1
      omega
    · rw [dif_neg hkn]; simp

lemma qExt_anti (f : ℝ → Fin n → ℝ) (hord : Antitone (N.qstar f)) : Antitone (N.qExt f) :=
  antitone_nat_of_succ_le (qExt_succ_le f hord)

lemma qExt_eq (f : ℝ → Fin n → ℝ) {k : ℕ} (h1 : k ≠ 0) (h2 : k ≤ n) :
    N.qExt f k = N.qstar f ⟨k - 1, by omega⟩ := by
  unfold Network.qExt; rw [dif_neg h1, dif_pos h2]

lemma qExt_big (f : ℝ → Fin n → ℝ) {k : ℕ} (h : n < k) : N.qExt f k = 0 := by
  unfold Network.qExt; rw [dif_neg (by omega), dif_neg (by omega)]

lemma part_exists (f : ℝ → Fin n → ℝ) (v : ENNReal) (hv : v ≠ ⊤) :
    ∃ k, k ≤ n ∧ N.qExt f (k + 1) ≤ v ∧ v < N.qExt f k := by
  have hP : ∃ k, N.qExt f (k + 1) ≤ v := ⟨n, by rw [qExt_big f (by omega)]; simp⟩
  classical
  refine ⟨Nat.find hP, Nat.find_min' hP (by rw [qExt_big f (by omega)]; simp),
    Nat.find_spec hP, ?_⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hP) with h | h
  · rw [h]; unfold Network.qExt; simp only [dif_pos]; exact lt_top_iff_ne_top.2 hv
  · have := Nat.find_min hP (show Nat.pred (Nat.find hP) < Nat.find hP by omega)
    rw [h]
    exact lt_of_not_ge this

lemma part_unique (f : ℝ → Fin n → ℝ) (hord : Antitone (N.qstar f)) (v : ENNReal) {k k' : ℕ}
    (h : N.qExt f (k + 1) ≤ v ∧ v < N.qExt f k) (h' : N.qExt f (k' + 1) ≤ v ∧ v < N.qExt f k') :
    k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := qExt_anti f hord (show k + 1 ≤ k' by omega)
    exact absurd (h'.2.trans_le (this.trans h.1)) (lt_irrefl _)
  · have := qExt_anti f hord (show k' + 1 ≤ k by omega)
    exact absurd (h.2.trans_le (this.trans h'.1)) (lt_irrefl _)

lemma default_iff (hN : N.Standing) (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hord : Antitone (N.qstar f)) (s : ℝ) (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ n)
    (h : N.qExt f (k + 1) ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < N.qExt f k) (i : Fin n) :
    N.clearingWealth (f s) i < 0 ↔ i.val < k := by
  rw [threshold hN f hf_mono hf_nonneg hf_rc s hs i]
  constructor
  · intro hlt
    by_contra hik
    push Not at hik
    have hk1 : k + 1 ≤ n := by have := i.isLt; omega
    have e := qExt_eq (N := N) f (show k + 1 ≠ 0 by omega) hk1
    rw [e] at h
    have : N.qstar f i ≤ N.qstar f ⟨k + 1 - 1, by omega⟩ := hord (show k + 1 - 1 ≤ i.val by omega)
    exact absurd (hlt.trans_le (this.trans h.1)) (lt_irrefl _)
  · intro hik
    have e := qExt_eq (N := N) f (show k ≠ 0 by omega) hk
    rw [e] at h
    have : N.qstar f ⟨k - 1, by omega⟩ ≤ N.qstar f i := hord (show i.val ≤ k - 1 by omega)
    exact h.2.trans_le this

lemma DeltaK_eq (k : ℕ) : N.DeltaK k = N.DeltaM (Network.firstBanks k) ∧
    N.deltaK k = N.deltaV (Network.firstBanks k) := by
  unfold Network.DeltaK Network.deltaK
  split_ifs with hk
  · subst hk
    have h0 : (Network.firstBanks 0 : Finset (Fin n)) = ∅ := by
      ext j; simp [Network.firstBanks]
    have hdg : Network.dg (∅ : Finset (Fin n)) = 0 := by
      ext a b; simp [Network.dg, diagonal]
    have hM : N.Mmat ∅ = 1 := by simp [Network.Mmat, hdg]
    rw [h0]
    refine ⟨?_, ?_⟩
    · simp [Network.DeltaM, hM, hdg]
    · simp [Network.deltaV, hM, hdg]
  · exact ⟨rfl, rfl⟩

theorem wealth_on_piece (hN : N.Standing) (f : ℝ → Fin n → ℝ)
    (hf_mono : MonotoneOn f (Set.Ici 0)) (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hord : Antitone (N.qstar f)) (s : ℝ) (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ n)
    (h : N.qExt f (k + 1) ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < N.qExt f k) :
    N.clearingWealth (f s) = N.DeltaK k *ᵥ f s - N.deltaK k := by
  have hS : Finset.univ.filter (fun i => N.clearingWealth (f s) i < 0) = Network.firstBanks k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Network.firstBanks]
    exact default_iff hN f hf_mono hf_nonneg hf_rc hord s hs hk h i
  rw [(DeltaK_eq k).1, (DeltaK_eq k).2, ← hS]
  exact piecewise hN _ (hf_nonneg s hs)

/-! ### Integration -/

section Integration

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma Ik_meas (f : ℝ → Fin n → ℝ) {q : Ω → ℝ} (hq : Measurable q) (k : ℕ) :
    MeasurableSet (N.Ik f q k) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (q ω)) := ENNReal.measurable_ofReal.comp hq
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

lemma sum_indicator_eq (f : ℝ → Fin n → ℝ) (hord : Antitone (N.qstar f)) (q : Ω → ℝ)
    (g : ℕ → Ω → ℝ) (T : Finset ℕ) (ω : Ω) {k0 : ℕ} (hω : ω ∈ N.Ik f q k0) :
    ∑ k ∈ T, (N.Ik f q k).indicator (g k) ω = if k0 ∈ T then g k0 ω else 0 := by
  have hother : ∀ k, k ≠ k0 → (N.Ik f q k).indicator (g k) ω = 0 := by
    intro k hk
    apply Set.indicator_of_notMem
    intro hk'
    exact hk (part_unique f hord _ hk' hω)
  split_ifs with hT
  · rw [Finset.sum_eq_single_of_mem k0 hT (fun k _ hk => hother k hk)]
    exact Set.indicator_of_mem hω _
  · exact Finset.sum_eq_zero (fun k hk => hother k (by rintro rfl; exact hT hk))

theorem main (hN : N.Standing)
    (q : Ω → ℝ) (hq : Measurable q) (hq0 : ∀ᵐ ω ∂P, 0 ≤ q ω)
    (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0)) (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hX : ∀ j, Integrable (fun ω => f (q ω) j) P)
    (hord : Antitone (N.qstar f)) (i : Fin n) :
    let term : ℕ → Fin n → ℝ := fun k =>
      N.DeltaK k *ᵥ (fun j => ∫ ω, (N.Ik f q k).indicator (fun ω => f (q ω) j) ω ∂P)
        - (P (N.Ik f q k)).toReal • N.deltaK k
    P {ω | N.clearingWealth (f (q ω)) i < 0} = P {ω | ENNReal.ofReal (q ω) < N.qstar f i} ∧
      ∫ ω, N.clearingWealth (f (q ω)) i ∂P = ∑ k ∈ Finset.range (n + 1), term k i ∧
      ∫ ω, N.payment (f (q ω)) i ∂P = N.pbar i + ∑ k ∈ Finset.Ioc i.val n, term k i ∧
      ∫ ω, N.equity (f (q ω)) i ∂P = ∑ k ∈ Finset.range (i.val + 1), term k i := by
  intro term
  set g : ℕ → Ω → ℝ := fun k ω => (N.DeltaK k *ᵥ f (q ω)) i - N.deltaK k i with hg
  -- integrability of the pieces
  have hgint : ∀ k, Integrable (g k) P := by
    intro k
    simp only [hg, mulVec, dotProduct]
    exact (integrable_finsetSum _ (fun j _ => (hX j).const_mul _)).sub (integrable_const _)
  have hgI : ∀ k, Integrable ((N.Ik f q k).indicator (g k)) P :=
    fun k => (hgint k).indicator (Ik_meas f hq k)
  -- the integral of each piece
  have hpiece : ∀ k, ∫ ω, (N.Ik f q k).indicator (g k) ω ∂P = term k i := by
    intro k
    have hI := Ik_meas (N := N) f hq k
    simp only [term, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [integral_indicator hI]
    simp only [integral_indicator hI, hg, mulVec, dotProduct]
    rw [integral_sub (integrable_finsetSum _ (fun j _ => ((hX j).const_mul _).integrableOn))
      (integrable_const _), integral_finsetSum _ (fun j _ => ((hX j).const_mul _).integrableOn)]
    simp only [integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def]
  have hsum : ∀ T : Finset ℕ, ∫ ω, ∑ k ∈ T, (N.Ik f q k).indicator (g k) ω ∂P =
      ∑ k ∈ T, term k i := by
    intro T
    rw [integral_finsetSum _ (fun k _ => hgI k)]
    exact Finset.sum_congr rfl (fun k _ => hpiece k)
  -- pointwise identification
  have hloc : ∀ ω, 0 ≤ q ω → ∃ k0, k0 ≤ n ∧ ω ∈ N.Ik f q k0 ∧
      N.clearingWealth (f (q ω)) = N.DeltaK k0 *ᵥ f (q ω) - N.deltaK k0 ∧
      (N.clearingWealth (f (q ω)) i < 0 ↔ i.val < k0) := by
    intro ω hω
    obtain ⟨k0, hk0, h⟩ := part_exists (N := N) f (ENNReal.ofReal (q ω)) ENNReal.ofReal_ne_top
    refine ⟨k0, hk0, h, ?_⟩
    exact ⟨wealth_on_piece hN f hf_mono hf_nonneg hf_rc hord _ hω hk0 h,
      default_iff hN f hf_mono hf_nonneg hf_rc hord _ hω hk0 h i⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply measure_congr
    filter_upwards [hq0] with ω hω
    exact propext (threshold hN f hf_mono hf_nonneg hf_rc _ hω i)
  · rw [← hsum]
    apply integral_congr_ae
    filter_upwards [hq0] with ω hω
    obtain ⟨k0, hk0, hmem, hV, _⟩ := hloc ω hω
    rw [sum_indicator_eq f hord q g _ ω hmem, if_pos (Finset.mem_range.2 (by omega)), hV]
    simp [hg]
  · have : ∫ ω, N.payment (f (q ω)) i ∂P = ∫ ω, (N.pbar i +
        ∑ k ∈ Finset.Ioc i.val n, (N.Ik f q k).indicator (g k) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hq0] with ω hω
      obtain ⟨k0, hk0, hmem, hV, hdef⟩ := hloc ω hω
      have hVi : N.clearingWealth (f (q ω)) i = g k0 ω := by rw [hV]; rfl
      rw [sum_indicator_eq f hord q g _ ω hmem]
      unfold Network.payment
      have hiff : k0 ∈ Finset.Ioc i.val n ↔ i.val < k0 := by
        simp only [Finset.mem_Ioc]; omega
      by_cases h : i.val < k0
      · rw [if_pos (hiff.2 h)]
        have hneg := hdef.2 h
        rw [max_eq_left (by linarith), ← hVi]; ring
      · rw [if_neg (fun h' => h (hiff.1 h'))]
        have hnn : 0 ≤ N.clearingWealth (f (q ω)) i := not_lt.1 (fun h' => h (hdef.1 h'))
        rw [max_eq_right (by linarith)]; ring
    rw [this, integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hgI k)),
      hsum, integral_const]
    simp
  · rw [← hsum]
    apply integral_congr_ae
    filter_upwards [hq0] with ω hω
    obtain ⟨k0, hk0, hmem, hV, hdef⟩ := hloc ω hω
    have hVi : N.clearingWealth (f (q ω)) i = g k0 ω := by rw [hV]; rfl
    rw [sum_indicator_eq f hord q g _ ω hmem]
    unfold Network.equity
    have hiff : k0 ∈ Finset.range (i.val + 1) ↔ ¬ i.val < k0 := by
      simp only [Finset.mem_range]; omega
    by_cases h : i.val < k0
    · rw [if_neg (fun h' => hiff.1 h' h)]
      exact max_eq_right (hdef.2 h).le
    · rw [if_pos (hiff.2 h), ← hVi]
      exact max_eq_left (not_lt.1 (fun h' => h (hdef.1 h')))

end Integration


/-! ### The fictitious default algorithm -/

/-- The linear clearing map with the default set frozen to `S`. -/
noncomputable def Lmap (N : Network n) (x : Fin n → ℝ) (S : Finset (Fin n)) (V : Fin n → ℝ) :
    Fin n → ℝ := fun i =>
  (1 - (1 - N.ax) * (if i ∈ S then 1 else 0)) * x i +
    (1 - (1 - N.aL) * (if i ∈ S then 1 else 0)) *
      ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * V j) - N.pbar i

lemma coef_mem (hN : N.Standing) (S : Finset (Fin n)) (i : Fin n) :
    0 ≤ 1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0) ∧
      1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0) ≤ 1 := by
  have h := hN.aL_mem; simp only [Set.mem_Icc] at h
  split_ifs <;> constructor <;> linarith

lemma coef_mem_x (hN : N.Standing) (S : Finset (Fin n)) (i : Fin n) :
    0 ≤ 1 - (1 - N.ax) * (if i ∈ S then (1:ℝ) else 0) ∧
      1 - (1 - N.ax) * (if i ∈ S then (1:ℝ) else 0) ≤ 1 := by
  have h := hN.ax_mem; simp only [Set.mem_Icc] at h
  split_ifs <;> constructor <;> linarith

/-- Maximum principle: a nonnegative matrix with column sums `< 1`. -/
lemma max_principle (A : Fin n → Fin n → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ j, ∑ i, A i j < 1) (D : Fin n → ℝ) (hD : ∀ i, ∑ j, A i j * D j ≤ D i) :
    0 ≤ D := by
  set M : Fin n → ℝ := fun j => max (-D j) 0 with hM
  have hM0 : ∀ j, 0 ≤ M j := fun j => le_max_right _ _
  have hMi : ∀ i, M i ≤ ∑ j, A i j * M j := by
    intro i
    have h0 : 0 ≤ ∑ j, A i j * M j := Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (hM0 j))
    apply max_le _ h0
    have : ∑ j, A i j * (-D j) ≤ ∑ j, A i j * M j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hA i j))
    have h2 : ∑ j, A i j * (-D j) = -∑ j, A i j * D j := by
      rw [← Finset.sum_neg_distrib]; congr 1; funext j; ring
    linarith [hD i]
  have hsum : ∑ j, (1 - ∑ i, A i j) * M j ≤ 0 := by
    have h1 : ∑ i, M i ≤ ∑ i, ∑ j, A i j * M j := Finset.sum_le_sum (fun i _ => hMi i)
    rw [Finset.sum_comm] at h1
    have h3 : ∑ j, (1 - ∑ i, A i j) * M j = ∑ j, M j - ∑ j, ∑ i, A i j * M j := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext j; rw [sub_mul, one_mul, Finset.sum_mul]
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (sub_nonneg.2 (hcol j).le) (hM0 j))).1 (le_antisymm hsum
      (Finset.sum_nonneg (fun j _ => mul_nonneg (sub_nonneg.2 (hcol j).le) (hM0 j))))
  intro j
  have := hz j (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · linarith [hcol j]
  · have : -D j ≤ 0 := by rw [← h]; exact le_max_left _ _
    simp only [Pi.zero_apply]; linarith

lemma Lmap_le_of_post (hN : N.Standing) (x : Fin n → ℝ) (S : Finset (Fin n))
    {V W : Fin n → ℝ} (hV : Lmap N x S V = V) (hW : W ≤ Lmap N x S W) : W ≤ V := by
  have := max_principle (fun i j => (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
      N.piM j i * (if j ∈ S then 1 else 0)) ?_ ?_ (V - W) ?_
  · intro i; have := this i; simp only [Pi.zero_apply, Pi.sub_apply] at this; linarith
  · intro i j
    exact mul_nonneg (mul_nonneg (coef_mem hN S i).1 (hN.piM_nonneg j i)) (by split_ifs <;> norm_num)
  · intro j
    calc ∑ i, (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i *
          (if j ∈ S then 1 else 0) ≤ ∑ i, N.piM j i := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 := coef_mem hN S i
          have h2 := hN.piM_nonneg j i
          have h3 : (if j ∈ S then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
          calc _ ≤ (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i * 1 :=
                mul_le_mul_of_nonneg_left h3 (mul_nonneg h1.1 h2)
            _ ≤ N.piM j i := by nlinarith [h1.2]
      _ < 1 := hN.row_sum_lt_one j
  · intro i
    have e1 := congrFun hV i
    have e2 := hW i
    unfold Lmap at e1 e2
    have : ∑ j, (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i *
        (if j ∈ S then 1 else 0) * (V - W) j =
        (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
          ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * V j) -
        (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
          ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * W j) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Pi.sub_apply]; ring
    rw [this, Pi.sub_apply]
    linarith

lemma Lmap_ge_of_pre (hN : N.Standing) (x : Fin n → ℝ) (S : Finset (Fin n))
    {V W : Fin n → ℝ} (hV : Lmap N x S V = V) (hW : Lmap N x S W ≤ W) : V ≤ W := by
  have := max_principle (fun i j => (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
      N.piM j i * (if j ∈ S then 1 else 0)) ?_ ?_ (W - V) ?_
  · intro i; have := this i; simp only [Pi.zero_apply, Pi.sub_apply] at this; linarith
  · intro i j
    exact mul_nonneg (mul_nonneg (coef_mem hN S i).1 (hN.piM_nonneg j i)) (by split_ifs <;> norm_num)
  · intro j
    calc ∑ i, (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i *
          (if j ∈ S then 1 else 0) ≤ ∑ i, N.piM j i := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 := coef_mem hN S i
          have h2 := hN.piM_nonneg j i
          have h3 : (if j ∈ S then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
          calc _ ≤ (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i * 1 :=
                mul_le_mul_of_nonneg_left h3 (mul_nonneg h1.1 h2)
            _ ≤ N.piM j i := by nlinarith [h1.2]
      _ < 1 := hN.row_sum_lt_one j
  · intro i
    have e1 := congrFun hV i
    have e2 := hW i
    unfold Lmap at e1 e2
    have : ∑ j, (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) * N.piM j i *
        (if j ∈ S then 1 else 0) * (W - V) j =
        (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
          ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * W j) -
        (1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0)) *
          ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * V j) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Pi.sub_apply]; ring
    rw [this, Pi.sub_apply]
    linarith

lemma Lmap_cmp (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) {S S' : Finset (Fin n)}
    (hSS : S ⊆ S') {V : Fin n → ℝ} (hV : -N.pbar ≤ V) (hneg : ∀ j ∈ S', j ∉ S → V j ≤ 0) :
    Lmap N x S' V ≤ Lmap N x S V := by
  intro i
  unfold Lmap
  set T' := ∑ j, N.piM j i * (N.pbar j + (if j ∈ S' then 1 else 0) * V j)
  set T := ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * V j)
  have hT' : 0 ≤ T' := Finset.sum_nonneg (fun j _ => by
    apply mul_nonneg (hN.piM_nonneg j i)
    have := hV j; have := hN.pbar_pos j; simp only [Pi.neg_apply] at *
    split_ifs <;> linarith)
  have hTT : T' ≤ T := Finset.sum_le_sum (fun j _ => by
    apply mul_le_mul_of_nonneg_left _ (hN.piM_nonneg j i)
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_pos (hSS hj)]
    · rw [if_neg hj]
      by_cases hj' : j ∈ S'
      · rw [if_pos hj']; linarith [hneg j hj' hj]
      · rw [if_neg hj'])
  have hxi := hx i
  have hc1 := coef_mem hN S' i
  have hc2 := coef_mem hN S i
  have hd1 := coef_mem_x hN S' i
  have hd2 := coef_mem_x hN S i
  have hle1 : 1 - (1 - N.aL) * (if i ∈ S' then (1:ℝ) else 0) ≤
      1 - (1 - N.aL) * (if i ∈ S then (1:ℝ) else 0) := by
    have h := hN.aL_mem; simp only [Set.mem_Icc] at h
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos (hSS hi)]
    · rw [if_neg hi]; split_ifs <;> linarith
  have hle2 : 1 - (1 - N.ax) * (if i ∈ S' then (1:ℝ) else 0) ≤
      1 - (1 - N.ax) * (if i ∈ S then (1:ℝ) else 0) := by
    have h := hN.ax_mem; simp only [Set.mem_Icc] at h
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos (hSS hi)]
    · rw [if_neg hi]; split_ifs <;> linarith
  have : T ≥ 0 := hT'.trans hTT
  nlinarith [mul_le_mul_of_nonneg_left hTT hc1.1, mul_le_mul_of_nonneg_right hle1 this,
    mul_le_mul_of_nonneg_right hle2 hxi]

lemma Lmap_default (x V : Fin n → ℝ) :
    Lmap N x (Finset.univ.filter (fun i => V i < 0)) V = N.PsiStar x V := by
  funext i
  unfold Lmap Network.PsiStar
  have hs : ∀ j, N.pbar j + (if j ∈ Finset.univ.filter (fun i => V i < 0) then (1:ℝ) else 0) * V j
      = N.pbar j - max (-V j) 0 := by
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  simp only [hs]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring

lemma fdaV_fixed (hN : N.Standing) (x : Fin n → ℝ) (k : ℕ) :
    Lmap N x (N.fdaZ x k) (N.fdaV x k) = N.fdaV x k := by
  cases k with
  | zero =>
    funext i
    simp only [Lmap, Network.fdaZ, Network.fdaV, Finset.notMem_empty, if_false, mul_zero,
      sub_zero, one_mul, zero_mul, add_zero, Pi.add_apply, Pi.sub_apply, mulVec, dotProduct,
      transpose_apply]
  | succ k =>
    set S := Finset.univ.filter (fun i => N.fdaV x k i < 0) with hS
    have hZ : N.fdaZ x (k + 1) = S := rfl
    set V := N.fdaV x (k + 1) with hVdef
    have hunit : IsUnit (N.Mmat S).det := isUnit_iff_ne_zero.mpr (Mmat_det_ne hN S)
    have hMV : N.Mmat S *ᵥ V = (1 - (1 - N.ax) • Network.dg S) *ᵥ x
        + ((1 - (1 - N.aL) • Network.dg S) * N.piMᵀ) *ᵥ N.pbar - N.pbar := by
      rw [hVdef]
      show N.Mmat S *ᵥ ((N.Mmat S)⁻¹ *ᵥ _) = _
      rw [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
    rw [hZ]
    funext i
    have e := congrFun hMV i
    set lam : Fin n → ℝ := fun i => if i ∈ S then 1 else 0 with hlam
    have hk : ∀ k, N.Mmat S i k * V k = (if i = k then V k else 0) -
        (1 - (1 - N.aL) * lam i) * (N.piM k i * (lam k * V k)) := fun k => by
      rw [Mmat_apply]; simp only [hlam]; split_ifs <;> ring
    have e1 : (N.Mmat S *ᵥ V) i = V i - (1 - (1 - N.aL) * lam i) *
        ∑ k, N.piM k i * (lam k * V k) := by
      simp only [mulVec, dotProduct, hk, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, ← Finset.mul_sum]
    have e2 : ((1 - (1 - N.ax) • Network.dg S) *ᵥ x) i = (1 - (1 - N.ax) * lam i) * x i := by
      rw [one_sub_smul_dg, mulVec_diagonal]
    have e3 : (((1 - (1 - N.aL) • Network.dg S) * N.piMᵀ) *ᵥ N.pbar) i =
        (1 - (1 - N.aL) * lam i) * ∑ k, N.piM k i * N.pbar k := by
      rw [← mulVec_mulVec, one_sub_smul_dg, mulVec_diagonal]
      simp only [mulVec, dotProduct, transpose_apply, hlam]
    rw [e1, Pi.sub_apply, Pi.add_apply, e2, e3] at e
    unfold Lmap
    have : ∑ j, N.piM j i * (N.pbar j + (if j ∈ S then 1 else 0) * V j) =
        ∑ k, N.piM k i * N.pbar k + ∑ k, N.piM k i * (lam k * V k) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun j _ => ?_); simp only [hlam]; ring
    rw [this]
    simp only [hlam] at e ⊢
    linarith

theorem fda_ge_G (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) (k : ℕ) :
    G N x ≤ N.fdaV x k := by
  obtain ⟨hfix, _, hlb⟩ := G_spec hN hx
  induction k with
  | zero =>
    show G N x ≤ ub N x
    rw [← hfix]; exact Psi_le hN hx _
  | succ k ih =>
    apply Lmap_le_of_post hN x (N.fdaZ x (k + 1)) (fdaV_fixed hN x (k + 1))
    have hGS : N.PsiStar x (G N x) = G N x := (G_isGreatest_PsiStar hN hx).1
    have hsub : N.fdaZ x (k + 1) ⊆ Finset.univ.filter (fun i => G N x i < 0) := by
      intro j hj
      simp only [Network.fdaZ, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_le_of_lt (ih j) hj
    calc G N x = Lmap N x (Finset.univ.filter (fun i => G N x i < 0)) (G N x) := by
          rw [Lmap_default, hGS]
      _ ≤ Lmap N x (N.fdaZ x (k + 1)) (G N x) := by
          apply Lmap_cmp hN hx hsub hlb
          intro j hj _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact hj.le

theorem fdaZ_mono (hN : N.Standing) {x : Fin n → ℝ} (hx : 0 ≤ x) (k : ℕ) :
    N.fdaZ x k ⊆ N.fdaZ x (k + 1) ∧ N.fdaV x (k + 1) ≤ N.fdaV x k := by
  have hlb : ∀ k, -N.pbar ≤ N.fdaV x k := fun k => (G_spec hN hx).2.2.trans (fda_ge_G hN hx k)
  have step : ∀ k, N.fdaZ x k ⊆ N.fdaZ x (k + 1) → N.fdaV x (k + 1) ≤ N.fdaV x k := by
    intro k hk
    apply Lmap_ge_of_pre hN x (N.fdaZ x (k + 1)) (fdaV_fixed hN x (k + 1))
    calc Lmap N x (N.fdaZ x (k + 1)) (N.fdaV x k) ≤ Lmap N x (N.fdaZ x k) (N.fdaV x k) := by
          apply Lmap_cmp hN hx hk (hlb k)
          intro j hj _
          simp only [Network.fdaZ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact hj.le
      _ = N.fdaV x k := fdaV_fixed hN x k
  have hz : ∀ k, N.fdaZ x k ⊆ N.fdaZ x (k + 1) := by
    intro k
    induction k with
    | zero => intro j hj; simp [Network.fdaZ] at hj
    | succ k ih =>
      have h := step k ih
      intro j hj
      simp only [Network.fdaZ, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_le_of_lt (h j) hj
  exact ⟨hz k, step k (hz k)⟩


theorem corA4 (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∀ S : Finset (Fin n), IsUnit (N.Mmat S).det) ∧
      ∃ k : ℕ, N.fdaZ x (k + 1) = N.fdaZ x k ∧ (∀ j < k, N.fdaZ x (j + 1) ≠ N.fdaZ x j) ∧
        N.fdaV x k = N.clearingWealth x := by
  refine ⟨fun S => isUnit_iff_ne_zero.mpr (Mmat_det_ne hN S), ?_⟩
  have hex : ∃ k, N.fdaZ x (k + 1) = N.fdaZ x k := by
    by_contra hne
    push Not at hne
    have hcard : ∀ k, k ≤ (N.fdaZ x k).card := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hss : N.fdaZ x k ⊂ N.fdaZ x (k + 1) :=
          Finset.ssubset_iff_subset_ne.2 ⟨(fdaZ_mono hN hx k).1, (hne k).symm⟩
        have := Finset.card_lt_card hss
        omega
    have h1 := hcard (n + 1)
    have h2 := Finset.card_le_univ (N.fdaZ x (n + 1))
    simp only [Fintype.card_fin] at h2
    omega
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj, ?_⟩
  have hk : N.fdaZ x (Nat.find hex + 1) = N.fdaZ x (Nat.find hex) := Nat.find_spec hex
  have hfix := fdaV_fixed hN x (Nat.find hex)
  rw [← hk] at hfix
  have hP : N.PsiStar x (N.fdaV x (Nat.find hex)) = N.fdaV x (Nat.find hex) := by
    rw [← Lmap_default]; exact hfix
  rw [clearingWealth_eq_G hN hx]
  exact le_antisymm ((G_isGreatest_PsiStar hN hx).2 hP) (fda_ge_G hN hx _)

end ComonoCore

open ComonoNetPricing.DebtEquity Matrix MeasureTheory

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∀ S : Finset (Fin n), IsUnit (N.Mmat S).det) ∧
      ∃ k : ℕ, N.fdaZ x (k + 1) = N.fdaZ x k ∧ (∀ j < k, N.fdaZ x (j + 1) ≠ N.fdaZ x j) ∧
        N.fdaV x k = N.clearingWealth x := by
  exact ComonoCore.corA4 hN x hx
