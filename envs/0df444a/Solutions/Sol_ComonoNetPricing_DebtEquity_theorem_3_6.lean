-- Prove2me | solution 1 for ComonoNetPricing.DebtEquity.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:33:57.6997+00:00
-- url     : https://prove2.me/submissions/bc34a36e-d4c6-4a7d-a247-2517dba7b0b7

import Mathlib
import Theorems.Thm_ComonoNetPricing_DebtEquity_piecewise_linear_wealth
import Theorems.Thm_ComonoNetPricing_DebtEquity_proposition_A_6
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

theorem threshold (hn : 0 < n) (hN : N.Standing) (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
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
    rw [← clearingWealth_eq_G hN (hf_nonneg t ht)]
    have := (ComonoNetPricing.DebtEquity.proposition_A_6 hn N hN _ _ (hf_nonneg s' hs'0)
      (hf_mono (Set.mem_Ici.2 hs'0) (Set.mem_Ici.2 ht) hs't.le)).1
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

lemma default_iff (hn : 0 < n) (hN : N.Standing) (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hord : Antitone (N.qstar f)) (s : ℝ) (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ n)
    (h : N.qExt f (k + 1) ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < N.qExt f k) (i : Fin n) :
    N.clearingWealth (f s) i < 0 ↔ i.val < k := by
  rw [threshold hn hN f hf_mono hf_nonneg hf_rc s hs i]
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

theorem wealth_on_piece (hn : 0 < n) (hN : N.Standing) (f : ℝ → Fin n → ℝ)
    (hf_mono : MonotoneOn f (Set.Ici 0)) (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hord : Antitone (N.qstar f)) (s : ℝ) (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ n)
    (h : N.qExt f (k + 1) ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < N.qExt f k) :
    N.clearingWealth (f s) = N.DeltaK k *ᵥ f s - N.deltaK k := by
  have hS : Finset.univ.filter (fun i => N.clearingWealth (f s) i < 0) = Network.firstBanks k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Network.firstBanks]
    exact default_iff hn hN f hf_mono hf_nonneg hf_rc hord s hs hk h i
  rw [(DeltaK_eq k).1, (DeltaK_eq k).2, ← hS]
  exact ComonoNetPricing.DebtEquity.piecewise_linear_wealth hn N hN _ (hf_nonneg s hs)

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

theorem main (hn : 0 < n) (hN : N.Standing)
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
    exact ⟨wealth_on_piece hn hN f hf_mono hf_nonneg hf_rc hord _ hω hk0 h,
      default_iff hn hN f hf_mono hf_nonneg hf_rc hord _ hω hk0 h i⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply measure_congr
    filter_upwards [hq0] with ω hω
    exact propext (threshold hn hN f hf_mono hf_nonneg hf_rc _ hω i)
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

end ComonoCore

open ComonoNetPricing.DebtEquity Matrix MeasureTheory

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
  exact ComonoCore.main P hn hN q hq hq0 f hf_mono hf_nonneg hf_rc hX hord i
