-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.lconvex_extension_is_polyhedral_when_polyhedral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:36:12.77449+00:00
-- url     : https://prove2.me/submissions/f1d803bd-b44b-4da3-9ac0-89ce64df2850

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LovaszExtension
import Theorems.Thm_DiscreteConvex_ConjugacyDualityC_lnat2_convex_is_integrally_convex
import Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_closure_basic_properties
import Theorems.Thm_DiscreteConvex_MConvexSetsB_lovasz_convex_iff_submodular

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsC

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma add_coe_inj {a b : WithTop ℝ} {r : ℝ}
    (h : a + (r : WithTop ℝ) = b + (r : WithTop ℝ)) : a = b := by
  cases a <;> cases b <;> simp [← WithTop.coe_add] at h ⊢
  exact h

private lemma trf_shift {g : (V → ℤ) → WithTop ℝ} {r : ℝ}
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ))
    (k : ℤ) (p : V → ℤ) :
    g (fun v => p v + k) = g p + (((k : ℝ) * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero =>
    simp
  | succ i ih =>
    have h1 : (fun v => p v + ((i : ℤ) + 1)) = (fun v => p v + (i : ℤ)) + 1 := by
      ext v; simp [Pi.add_apply, add_assoc]
    rw [h1, hr, ih, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring
  | pred i ih =>
    apply add_coe_inj (r := r)
    have h1 := hr (fun v => p v + (-(i : ℤ) - 1))
    have h2 : (fun v => p v + (-(i : ℤ) - 1)) + 1 = (fun v => p v + (-(i : ℤ))) := by
      ext v; simp [Pi.add_apply]; ring
    rw [h2, ih] at h1
    rw [← h1, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring

private lemma sbf_trf_imp_lnatC (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    DiscreteConvex.ConjugacyDualityC.LNaturalConvex g := by
  rcases hg with ⟨hSBF, r, hr⟩
  constructor
  · intro x y
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL
    have hx : g (fun v => x (some v) - x none) =
        g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-x none) (fun v => x (some v))
      have h1 : (fun v => x (some v) + -x none) = (fun v => x (some v) - x none) := by
        ext v; ring
      rw [h1] at h0
      simpa using h0
    have hy : g (fun v => y (some v) - y none) =
        g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-y none) (fun v => y (some v))
      have h1 : (fun v => y (some v) + -y none) = (fun v => y (some v) - y none) := by
        ext v; ring
      rw [h1] at h0
      simpa using h0
    have hsup : g (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) =
        g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-(x ⊔ y) none) (fun v => (x ⊔ y) (some v))
      have h1 : (fun v => (x ⊔ y) (some v) + -(x ⊔ y) none) =
          (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) := by
        ext v; ring
      have h2 : (fun v => (x ⊔ y) (some v)) = (fun v => x (some v)) ⊔ (fun v => y (some v)) := rfl
      rw [h1, h2] at h0
      simpa using h0
    have hinf : g (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) =
        g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
          (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-(x ⊓ y) none) (fun v => (x ⊓ y) (some v))
      have h1 : (fun v => (x ⊓ y) (some v) + -(x ⊓ y) none) =
          (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) := by
        ext v; ring
      have h2 : (fun v => (x ⊓ y) (some v)) = (fun v => x (some v)) ⊓ (fun v => y (some v)) := rfl
      rw [h1, h2] at h0
      simpa using h0
    rw [hx, hy, hsup, hinf]
    have hadd_lhs :
        (g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ)) +
        (g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ)) =
        (g (fun v => x (some v)) + g (fun v => y (some v))) +
        (((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]
      ac_rfl
    have hadd_rhs :
        (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) +
        (g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
          (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) =
        (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          g ((fun v => x (some v)) ⊓ (fun v => y (some v)))) +
        (((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]
      ac_rfl
    rw [hadd_lhs, hadd_rhs]
    have hnone :
        ((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) =
        ((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) := by
      have hmm : ((x ⊔ y) none : ℤ) + ((x ⊓ y) none : ℤ) = x none + y none :=
        max_add_min (x none) (y none)
      have hmmR : (((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) =
          (x none : ℝ) + (y none : ℝ) := by
        exact_mod_cast hmm
      calc (-(x none : ℝ)) * r + (-(y none : ℝ)) * r
        _ = -((x none : ℝ) + (y none : ℝ)) * r := by ring
        _ = -(((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) * r := by rw [hmmR]
        _ = (-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r := by ring
    rw [hnone]
    exact add_le_add (hSBF (fun v => x (some v)) (fun v => y (some v))) le_rfl
  · refine ⟨0, fun x => ?_⟩
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL
    have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
      ext v; simp [Pi.add_apply]
    rw [h1]
    simp

private noncomputable def zeroInd : (V → ℤ) → WithTop ℝ :=
  fun p => if p = 0 then 0 else ⊤

private lemma zeroInd_lnatC : DiscreteConvex.ConjugacyDualityC.LNaturalConvex (zeroInd (V := V)) := by
  constructor
  · intro x y
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    by_cases hx : (fun v => x (some v) - x none) = 0
    · by_cases hy : (fun v => y (some v) - y none) = 0
      · have hsup : (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.sup_apply, hxv, hyv]
        have hinf : (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.inf_apply, hxv, hyv]
        simp only [hx, hy, hsup, hinf, ite_true, add_zero, le_rfl]
      · simp [hy]
    · simp [hx]
  · refine ⟨0, fun x => ?_⟩
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
      ext v; simp [Pi.add_apply]
    rw [h1]
    simp

private lemma sbf_trf_imp_ic (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    DiscreteConvex.ConjugacyDualityC.IsIntegrallyConvexFunction g := by
  apply DiscreteConvex.ConjugacyDualityC.lnat2_convex_is_integrally_convex.1
  refine ⟨g, zeroInd, sbf_trf_imp_lnatC g hg, zeroInd_lnatC, ?_, ?_⟩
  · intro p
    have hle : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≤
        DiscreteConvex.ConjugacyDualityC.InfConvE g zeroInd p := by
      apply le_sInf
      rintro L ⟨p1, p2, rfl, rfl⟩
      by_cases hp2 : p2 = 0
      · subst hp2
        have h0 : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd (0 : V → ℤ)) = 0 := by
          dsimp [DiscreteConvex.ConjugacyDualityC.ToEReal, zeroInd]
          rw [if_pos rfl]
          rfl
        rw [add_zero, h0, add_zero]
      · have htop : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd p2) = ⊤ := by
          dsimp [DiscreteConvex.ConjugacyDualityC.ToEReal, zeroInd]
          rw [if_neg hp2]
          rfl
        rw [htop]
        cases gp1 : g p1 with
        | top =>
          change DiscreteConvex.ConjugacyDualityC.ToEReal (g (p1 + p2)) ≤ (⊤ : EReal) + ⊤
          rw [EReal.top_add_top]
          exact le_top
        | coe a =>
          change DiscreteConvex.ConjugacyDualityC.ToEReal (g (p1 + p2)) ≤ (a : EReal) + ⊤
          rw [EReal.coe_add_top]
          exact le_top
    intro hbot
    rw [hbot] at hle
    have hne : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≠ ⊥ := WithBot.coe_ne_bot
    exact hne (le_bot_iff.mp hle)
  · ext p
    unfold DiscreteConvex.ConjugacyDualityC.InfConv
    symm
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨p, 0, by simp, ?_⟩
      simp [zeroInd]
    · rintro L ⟨p1, p2, rfl, rfl⟩
      by_cases hp2 : p2 = 0
      · subst hp2
        simp [zeroInd]
      · simp [zeroInd, hp2]

private lemma bddBelow_convexClosureValOn (g : (V → ℤ) → WithTop ℝ)
    (S : Finset (V → ℤ)) (x : V → ℝ) :
    BddBelow {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
      L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} := by
  refine ⟨((∑ y ∈ S, -|(g y).untopD 0| : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨lam, h0, h1, _, _, rfl⟩
  rw [WithTop.coe_le_coe]
  apply Finset.sum_le_sum
  intro y hy
  have hlam0 : 0 ≤ lam y := h0 y hy
  have hlam1 : lam y ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum h0 hy
  have habs : -|(g y).untopD 0| ≤ (g y).untopD 0 := neg_abs_le ((g y).untopD 0)
  have habs0 : 0 ≤ |(g y).untopD 0| := abs_nonneg ((g y).untopD 0)
  nlinarith

private noncomputable def lovaszList (rho : Finset V → WithTop ℝ) (p : V → ℝ) : List ℝ → WithTop ℝ
  | [] => 0
  | [a] => PosScalarMul a (rho (Finset.univ.filter (fun v => a ≤ p v)))
  | a :: b :: rest =>
      PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v))) +
        lovaszList rho p (b :: rest)

private lemma posScalarMul_zero (x : WithTop ℝ) : PosScalarMul 0 x = 0 := by
  cases x <;> simp [PosScalarMul]

private lemma posScalarMul_add_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : WithTop ℝ) :
    PosScalarMul (a + b) x = PosScalarMul a x + PosScalarMul b x := by
  cases x with
  | top =>
    have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    simp [PosScalarMul, hab, ha0, hb0]
  | coe r =>
    dsimp [PosScalarMul]
    exact_mod_cast add_mul a b r

private lemma posScalarMul_sub_add_coe {a c r : ℝ} :
    PosScalarMul (a - c) (r : WithTop ℝ) + PosScalarMul c (r : WithTop ℝ) =
      PosScalarMul a (r : WithTop ℝ) := by
  dsimp [PosScalarMul]
  exact_mod_cast (by ring : (a - c) * r + c * r = a * r)

private lemma posScalarMul_le_add_of_nonneg {c : ℝ} (hc : 0 ≤ c) {x y z w : WithTop ℝ}
    (h : z + w ≤ x + y) :
    PosScalarMul c z + PosScalarMul c w ≤ PosScalarMul c x + PosScalarMul c y := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp [posScalarMul_zero]
  · by_cases hx : x = ⊤
    · subst hx
      simp [PosScalarMul, ne_of_gt hc_pos]
    · by_cases hy : y = ⊤
      · subst hy
        simp [PosScalarMul, ne_of_gt hc_pos]
      · lift x to ℝ using hx
        lift y to ℝ using hy
        have hzw_ne : z + w ≠ ⊤ := by
          intro htop
          rw [htop] at h
          exact WithTop.coe_ne_top (top_le_iff.mp (h.trans_eq (WithTop.coe_add x y).symm))
        have hz : z ≠ ⊤ := fun htop => hzw_ne (by simp [htop])
        have hw : w ≠ ⊤ := fun htop => hzw_ne (by simp [htop])
        lift z to ℝ using hz
        lift w to ℝ using hw
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
        dsimp [PosScalarMul]
        exact_mod_cast (by nlinarith : c * z + c * w ≤ c * x + c * y)

private lemma lovaszList_eq_sum (rho : Finset V → WithTop ℝ) (p : V → ℝ) :
    ∀ (L : List ℝ),
      lovaszList rho p L =
        (∑ i ∈ Finset.range (L.length - 1),
            PosScalarMul (L.getD i 0 - L.getD (i + 1) 0)
              (rho (Finset.univ.filter (fun v => L.getD i 0 ≤ p v)))) +
          PosScalarMul (L.getD (L.length - 1) 0)
            (rho (Finset.univ.filter (fun v => L.getD (L.length - 1) 0 ≤ p v)))
  | [] => by simp [lovaszList, posScalarMul_zero]
  | [a] => by simp [lovaszList]
  | a :: b :: rest => by
      have ih := lovaszList_eq_sum rho p (b :: rest)
      simp only [lovaszList, ih, List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      ac_rfl

private lemma lovaszList_sortedValues (rho : Finset V → WithTop ℝ) (p : V → ℝ) :
    lovaszList rho p (SortedValues p) = DiscreteConvex.MConvexSetsB.LovaszExtension rho p := by
  unfold DiscreteConvex.MConvexSetsB.LovaszExtension DiscreteConvex.MConvexSetsB.LevelSet
  change lovaszList rho p (SortedValues p) =
    (∑ i ∈ Finset.range ((SortedValues p).length - 1),
        PosScalarMul ((SortedValues p).getD i 0 - (SortedValues p).getD (i + 1) 0)
          (rho (Finset.univ.filter (fun v => (SortedValues p).getD (i + 1 - 1) 0 ≤ p v)))) +
      PosScalarMul ((SortedValues p).getD ((SortedValues p).length - 1) 0)
        (rho (Finset.univ.filter (fun v => (SortedValues p).getD ((SortedValues p).length - 1) 0 ≤ p v)))
  rw [lovaszList_eq_sum]
  by_cases hlen : (SortedValues p).length = 0
  · simp [hlen]
  · simp

private noncomputable def insLow (c : ℝ) : List ℝ → List ℝ
  | [] => [c]
  | a :: rest => if c = a then a :: rest else if a < c then c :: a :: rest else a :: insLow c rest

private lemma mem_insLow {c x : ℝ} : ∀ {L : List ℝ}, x ∈ insLow c L ↔ x = c ∨ x ∈ L
  | [] => by simp [insLow]
  | a :: rest => by
      simp only [insLow]
      split_ifs with h1 h2
      · subst h1; simp
      · simp
      · simp [mem_insLow]; tauto

private lemma pairwise_insLow (c : ℝ) : ∀ {L : List ℝ},
    List.Pairwise (· > ·) L → List.Pairwise (· > ·) (insLow c L)
  | [], _ => List.pairwise_singleton _ _
  | a :: rest, hpw => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hrest⟩
      simp only [insLow]
      split_ifs with h1 h2
      · exact hpw
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, hpw⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h2
        · exact lt_trans (ha x hx) h2
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, pairwise_insLow c hrest⟩
        rcases mem_insLow.mp hx with rfl | hx
        · exact lt_of_le_of_ne (not_lt.mp h2) h1
        · exact ha x hx

private lemma insLow_ne_nil (c : ℝ) (L : List ℝ) : insLow c L ≠ [] := by
  cases L with
  | nil => simp [insLow]
  | cons a rest =>
    simp only [insLow]
    split_ifs <;> simp

private lemma eq_of_pairwise_gt : ∀ {L₁ L₂ : List ℝ},
    List.Pairwise (· > ·) L₁ → List.Pairwise (· > ·) L₂ →
    (∀ x, x ∈ L₁ ↔ x ∈ L₂) → L₁ = L₂
  | [], [], _, _, _ => rfl
  | a :: L₁, [], _, _, hmem => False.elim ((List.not_mem_nil) ((hmem a).mp List.mem_cons_self))
  | [], b :: L₂, _, _, hmem => False.elim ((List.not_mem_nil) ((hmem b).mpr List.mem_cons_self))
  | a :: L₁, b :: L₂, hpw₁, hpw₂, hmem => by
      rcases List.pairwise_cons.mp hpw₁ with ⟨ha, hrest₁⟩
      rcases List.pairwise_cons.mp hpw₂ with ⟨hb, hrest₂⟩
      have hab : a = b := by
        have ha_in : a ∈ b :: L₂ := (hmem a).mp List.mem_cons_self
        have hb_in : b ∈ a :: L₁ := (hmem b).mpr List.mem_cons_self
        rcases List.mem_cons.mp ha_in with rfl | ha_in
        · rfl
        · rcases List.mem_cons.mp hb_in with rfl | hb_in
          · rfl
          · exact False.elim (lt_asymm (hb a ha_in) (ha b hb_in))
      subst hab
      congr 1
      refine eq_of_pairwise_gt hrest₁ hrest₂ (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · have hx' : x ∈ a :: L₂ := (hmem x).mp (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact False.elim (lt_irrefl x (ha x hx))
        · exact hx'
      · have hx' : x ∈ a :: L₁ := (hmem x).mpr (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact False.elim (lt_irrefl x (hb x hx))
        · exact hx'

private lemma pairwise_gt_sort (s : Finset ℝ) : List.Pairwise (· > ·) (s.sort (· ≥ ·)) := by
  have hle := Finset.pairwise_sort s (· ≥ ·)
  have hnd := Finset.sort_nodup s (· ≥ ·)
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  rw [List.pairwise_iff_getElem] at hle ⊢
  intro i j hi hj hij
  exact lt_of_le_of_ne (hle i j hi hj hij) (Ne.symm (hnd i j hi hj hij))

private lemma lovaszList_insLow_lt (rho : Finset V → WithTop ℝ)
    (hrhoV : rho Finset.univ ≠ ⊤) (p : V → ℝ) (c : ℝ) :
    ∀ (L : List ℝ) (_ : L ≠ []),
      List.Pairwise (· > ·) L →
      (∀ v : V, p v ∈ L ∨ ∀ x ∈ L, x < p v) →
      (∀ a ∈ L.head?, c < a) →
      lovaszList rho p (insLow c L) = lovaszList rho p L
  | [], hL, _, _, _ => False.elim (hL rfl)
  | [a], _, hpw, hcov, hlt => by
      have hca : c < a := hlt a rfl
      have hne : c ≠ a := ne_of_lt hca
      have hnot : ¬ a < c := not_lt_of_gt hca
      simp only [insLow, hne, hnot, ite_false]
      have hfa : Finset.univ.filter (fun v => a ≤ p v) = Finset.univ := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases hcov v with hv | hv
        · simp only [List.mem_singleton] at hv; linarith
        · exact le_of_lt (hv a (List.mem_singleton.mpr rfl))
      have hfc : Finset.univ.filter (fun v => c ≤ p v) = Finset.univ := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have : a ≤ p v := by
          have : v ∈ Finset.univ.filter (fun v => a ≤ p v) := by rw [hfa]; exact Finset.mem_univ v
          exact (Finset.mem_filter.mp this).2
        linarith
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hrhoV
      simp only [lovaszList, hfa, hfc, ← hr]
      exact posScalarMul_sub_add_coe
  | a :: b :: rest, _, hpw, hcov, hlt => by
      have hca : c < a := hlt a rfl
      have hne : c ≠ a := ne_of_lt hca
      have hnot : ¬ a < c := not_lt_of_gt hca
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab : a > b := ha_gt b List.mem_cons_self
      have hcov' : ∀ v : V, p v ∈ b :: rest ∨ ∀ x ∈ b :: rest, x < p v := by
        intro v
        rcases hcov v with hv | hv
        · rcases List.mem_cons.mp hv with hva | hva'
          · right
            intro x hx
            rw [hva]
            exact ha_gt x hx
          · left; exact hva'
        · right
          intro x hx
          exact hv x (List.mem_cons_of_mem a hx)
      by_cases hcb : c = b
      · subst hcb
        simp [insLow, hne, hnot]
      · by_cases hbc : b < c
        · simp only [insLow, hne, hnot, hcb, hbc, ite_true, ite_false, lovaszList]
          have hfc_eq_fa : Finset.univ.filter (fun v => c ≤ p v) =
              Finset.univ.filter (fun v => a ≤ p v) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun hcp => ?_, fun hap => le_trans (le_of_lt hca) hap⟩
            rcases hcov v with hv | hv
            · rcases List.mem_cons.mp hv with hva | hva'
              · linarith
              · rcases List.mem_cons.mp hva' with hvb | hvrest
                · linarith
                · have hbx : b > p v := (List.pairwise_cons.mp hpw').1 (p v) hvrest
                  linarith
            · exact le_of_lt (hv a List.mem_cons_self)
          rw [hfc_eq_fa, ← add_assoc]
          congr 1
          have h1 : 0 < a - c := sub_pos.mpr hca
          have h2 : 0 < c - b := sub_pos.mpr hbc
          have hsum : (a - c) + (c - b) = a - b := by ring
          rw [← posScalarMul_add_of_pos h1 h2, hsum]
        · have hcb' : c < b := lt_of_le_of_ne (not_lt.mp hbc) hcb
          have ih := lovaszList_insLow_lt rho hrhoV p c (b :: rest) (by simp) hpw' hcov'
            (by intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; subst hx; exact hcb')
          have h_ins_b : insLow c (b :: rest) = b :: insLow c rest := by
            simp [insLow, hcb, hbc]
          have h_ins_a : insLow c (a :: b :: rest) = a :: b :: insLow c rest := by
            simp [insLow, hne, hnot, hcb, hbc]
          rw [h_ins_b] at ih
          rw [h_ins_a]
          simp only [lovaszList, ih]

private lemma lovaszList_insLow (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (p : V → ℝ) (c : ℝ) (L : List ℝ) (hL : L ≠ [])
    (hpw : List.Pairwise (· > ·) L) (hmem : ∀ v : V, p v ∈ L) :
    lovaszList rho p (insLow c L) = lovaszList rho p L := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons a rest =>
    by_cases hca : c = a
    · subst hca; simp [insLow]
    · by_cases hac : a < c
      · have h_ins : insLow c (a :: rest) = c :: a :: rest := by simp [insLow, hca, hac]
        rw [h_ins]
        have hfc_empty : Finset.univ.filter (fun v => c ≤ p v) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro v _
          rw [not_le]
          have hv : p v ∈ a :: rest := hmem v
          rcases List.mem_cons.mp hv with hva | hvrest
          · linarith
          · have hap : a > p v := (List.pairwise_cons.mp hpw).1 (p v) hvrest
            linarith
        simp only [lovaszList, hfc_empty, hrho.1]
        have h0 : PosScalarMul (c - a) 0 = 0 := by simp [PosScalarMul]
        rw [h0, zero_add]
      · have hca' : c < a := lt_of_le_of_ne (not_lt.mp hac) hca
        exact lovaszList_insLow_lt rho hrho.2.1 p c (a :: rest) (by simp) hpw
          (fun v => Or.inl (hmem v))
          (by intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; subst hx; exact hca')

private lemma lovaszList_foldr_insLow (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (p : V → ℝ) :
    ∀ (U : List ℝ) (L : List ℝ),
      L ≠ [] → List.Pairwise (· > ·) L → (∀ v : V, p v ∈ L) →
      lovaszList rho p (U.foldr insLow L) = lovaszList rho p L ∧
      U.foldr insLow L ≠ [] ∧
      List.Pairwise (· > ·) (U.foldr insLow L) ∧
      (∀ x, x ∈ U.foldr insLow L ↔ x ∈ U ∨ x ∈ L)
  | [], L, hL, hpw, hmem => ⟨rfl, hL, hpw, fun x => by simp⟩
  | c :: U, L, hL, hpw, hmem => by
      rcases lovaszList_foldr_insLow rho hrho p U L hL hpw hmem with ⟨heq, hne', hpw', hmem'⟩
      have hmem_p : ∀ v : V, p v ∈ U.foldr insLow L := fun v => (hmem' (p v)).mpr (Or.inr (hmem v))
      refine ⟨?_, insLow_ne_nil c _, pairwise_insLow c hpw', fun x => ?_⟩
      · simp only [List.foldr_cons]
        rw [lovaszList_insLow rho hrho p c (U.foldr insLow L) hne' hpw' hmem_p, heq]
      · simp only [List.foldr_cons, mem_insLow, hmem', List.mem_cons]
        tauto

private lemma lovasz_eq_lovaszList_of_mem [Nonempty V] (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (p : V → ℝ) (L : List ℝ)
    (hpw : List.Pairwise (· > ·) L) (hmem : ∀ v : V, p v ∈ L) :
    DiscreteConvex.MConvexSetsB.LovaszExtension rho p = lovaszList rho p L := by
  have hSV_ne : SortedValues p ≠ [] := by
    unfold SortedValues
    intro h
    have hemp : (Finset.image p Finset.univ).sort (· ≥ ·) = [] := h
    have ⟨v₀⟩ := ‹Nonempty V›
    have hmem0 : p v₀ ∈ (Finset.image p Finset.univ).sort (· ≥ ·) :=
      (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_image_of_mem p (Finset.mem_univ v₀))
    rw [hemp] at hmem0
    exact List.not_mem_nil hmem0
  have hSV_pw : List.Pairwise (· > ·) (SortedValues p) := pairwise_gt_sort _
  have hSV_mem : ∀ v : V, p v ∈ SortedValues p := fun v =>
    (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_image_of_mem p (Finset.mem_univ v))
  rcases lovaszList_foldr_insLow rho hrho p L (SortedValues p) hSV_ne hSV_pw hSV_mem with
    ⟨heq, _, hpw_fold, hmem_fold⟩
  have hL_eq : L.foldr insLow (SortedValues p) = L := by
    refine eq_of_pairwise_gt hpw_fold hpw (fun x => ?_)
    rw [hmem_fold]
    refine ⟨fun hx => ?_, fun hx => Or.inl hx⟩
    rcases hx with hx | hx
    · exact hx
    · have hx' := (Finset.mem_sort (· ≥ ·)).mp hx
      rcases Finset.mem_image.mp hx' with ⟨v, _, rfl⟩
      exact hmem v
  rw [← lovaszList_sortedValues, ← heq, hL_eq]

private noncomputable def roundAt1D (r a : ℝ) : ℤ :=
  ⌊r⌋ + if a ≤ r - (⌊r⌋ : ℝ) then 1 else 0

private noncomputable def roundAt (x : V → ℝ) (a : ℝ) : V → ℤ :=
  fun v => roundAt1D (x v) a

private noncomputable def roundListSum (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : List ℝ → WithTop ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      PosScalarMul (a - b) (g (roundAt x a)) + roundListSum g x (b :: rest)

private noncomputable def lamL (x : V → ℝ) : List ℝ → (V → ℤ) → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, y =>
      (if y = roundAt x a then a - b else 0) + lamL x (b :: rest) y

private lemma roundAt_mono_1D {r₁ r₂ a : ℝ} (hr : r₁ ≤ r₂) :
    roundAt1D r₁ a ≤ roundAt1D r₂ a := by
  dsimp only [roundAt1D]
  have hfl : ⌊r₁⌋ ≤ ⌊r₂⌋ := Int.floor_mono hr
  by_cases heq : ⌊r₁⌋ = ⌊r₂⌋
  · rw [heq]
    split_ifs with h1 h2
    · omega
    · exfalso; apply h2; rw [← heq]; linarith
    · omega
    · omega
  · have hlt : ⌊r₁⌋ + 1 ≤ ⌊r₂⌋ := by omega
    split_ifs <;> omega

private lemma roundAt_sup (p q : V → ℝ) (a : ℝ) :
    roundAt (p ⊔ q) a = roundAt p a ⊔ roundAt q a := by
  ext v
  change roundAt1D (max (p v) (q v)) a = max (roundAt1D (p v) a) (roundAt1D (q v) a)
  rcases le_total (p v) (q v) with hpq | hqp
  · rw [max_eq_right hpq, max_eq_right (roundAt_mono_1D hpq)]
  · rw [max_eq_left hqp, max_eq_left (roundAt_mono_1D hqp)]

private lemma roundAt_inf (p q : V → ℝ) (a : ℝ) :
    roundAt (p ⊓ q) a = roundAt p a ⊓ roundAt q a := by
  ext v
  change roundAt1D (min (p v) (q v)) a = min (roundAt1D (p v) a) (roundAt1D (q v) a)
  rcases le_total (p v) (q v) with hpq | hqp
  · rw [min_eq_left hpq, min_eq_left (roundAt_mono_1D hpq)]
  · rw [min_eq_right hqp, min_eq_right (roundAt_mono_1D hqp)]

private lemma roundListSum_sbf (g : (V → ℤ) → WithTop ℝ) (hSBF : SBF g) (p q : V → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L →
      roundListSum g (p ⊔ q) L + roundListSum g (p ⊓ q) L ≤
        roundListSum g p L + roundListSum g q L
  | [], _ => by simp [roundListSum]
  | [_], _ => by simp [roundListSum]
  | a :: b :: rest, hpw => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hpw'⟩
      have hab : 0 ≤ a - b := le_of_lt (sub_pos.mpr (ha b List.mem_cons_self))
      have ih := roundListSum_sbf g hSBF p q (b :: rest) hpw'
      have hhead :
          PosScalarMul (a - b) (g (roundAt (p ⊔ q) a)) +
            PosScalarMul (a - b) (g (roundAt (p ⊓ q) a)) ≤
          PosScalarMul (a - b) (g (roundAt p a)) +
            PosScalarMul (a - b) (g (roundAt q a)) := by
        rw [roundAt_sup, roundAt_inf]
        exact posScalarMul_le_add_of_nonneg hab (hSBF (roundAt p a) (roundAt q a))
      simp only [roundListSum]
      calc (PosScalarMul (a - b) (g (roundAt (p ⊔ q) a)) + roundListSum g (p ⊔ q) (b :: rest)) +
            (PosScalarMul (a - b) (g (roundAt (p ⊓ q) a)) + roundListSum g (p ⊓ q) (b :: rest))
        _ = (PosScalarMul (a - b) (g (roundAt (p ⊔ q) a)) +
              PosScalarMul (a - b) (g (roundAt (p ⊓ q) a))) +
            (roundListSum g (p ⊔ q) (b :: rest) + roundListSum g (p ⊓ q) (b :: rest)) := by ac_rfl
        _ ≤ (PosScalarMul (a - b) (g (roundAt p a)) +
              PosScalarMul (a - b) (g (roundAt q a))) +
            (roundListSum g p (b :: rest) + roundListSum g q (b :: rest)) := add_le_add hhead ih
        _ = (PosScalarMul (a - b) (g (roundAt p a)) + roundListSum g p (b :: rest)) +
            (PosScalarMul (a - b) (g (roundAt q a)) + roundListSum g q (b :: rest)) := by ac_rfl

private lemma roundAt_mem_neighborhood (x : V → ℝ) {a : ℝ} (ha : 0 < a) :
    roundAt x a ∈ DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x := by
  simp only [DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset,
    Fintype.mem_piFinset, Finset.mem_Icc, roundAt, roundAt1D]
  intro v
  split_ifs with h
  · refine ⟨by omega, ?_⟩
    have hlt : (⌊x v⌋ : ℝ) < x v := by linarith
    have hle : ⌊x v⌋ + 1 ≤ ⌈x v⌉ := by
      have : ¬ (⌈x v⌉ ≤ ⌊x v⌋) := by
        intro hce
        have h1 : x v ≤ (⌈x v⌉ : ℝ) := Int.le_ceil (x v)
        have h2 : (⌈x v⌉ : ℝ) ≤ (⌊x v⌋ : ℝ) := by exact_mod_cast hce
        linarith
      omega
    exact hle
  · have hfc : ⌊x v⌋ ≤ ⌈x v⌉ := Int.floor_le_ceil (x v)
    exact ⟨by omega, by omega⟩

private lemma lamL_nonneg (x : V → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L → ∀ y : V → ℤ, 0 ≤ lamL x L y
  | [], _, _ => le_rfl
  | [_], _, _ => le_rfl
  | a :: b :: rest, hpw, y => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hpw'⟩
      have hab : 0 ≤ a - b := le_of_lt (sub_pos.mpr (ha b List.mem_cons_self))
      simp only [lamL]
      apply add_nonneg
      · split_ifs <;> linarith
      · exact lamL_nonneg x (b :: rest) hpw' y

private lemma sum_lamL_mul (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ)
    (Sx : Finset (V → ℤ))
    (hSx : Sx = Finset.filter (fun y => y ∈ DomZ g) (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x))
    (F : (V → ℤ) → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L → (∀ c ∈ L, 0 ≤ c) →
      roundListSum g x L ≠ ⊤ →
      ∑ y ∈ Sx, lamL x L y * F y =
        match L with
        | [] => 0
        | [_] => 0
        | a :: b :: rest =>
            (a - b) * F (roundAt x a) + ∑ y ∈ Sx, lamL x (b :: rest) y * F y
  | [], _, _, _ => by simp [lamL]
  | [_], _, _, _ => by simp [lamL]
  | a :: b :: rest, hpw, h0, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, _⟩
      have hab_lt : b < a := ha b List.mem_cons_self
      have hb0 : 0 ≤ b := h0 b (List.mem_cons_of_mem a List.mem_cons_self)
      have ha_pos : 0 < a := lt_of_le_of_lt hb0 hab_lt
      have hab_ne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hab_lt)
      simp only [roundListSum] at hne_top
      have hhead_ne_top : PosScalarMul (a - b) (g (roundAt x a)) ≠ ⊤ :=
        fun htop => hne_top (by simp [htop])
      have hdom_a : roundAt x a ∈ DomZ g := by
        intro htop
        apply hhead_ne_top
        simp [PosScalarMul, htop, hab_ne]
      have ha_Sx : roundAt x a ∈ Sx := by
        rw [hSx, Finset.mem_filter]
        exact ⟨roundAt_mem_neighborhood x ha_pos, hdom_a⟩
      simp only [lamL, add_mul, Finset.sum_add_distrib]
      congr 1
      have hite : (∑ y ∈ Sx, (if y = roundAt x a then a - b else 0) * F y) =
          ∑ y ∈ Sx, if y = roundAt x a then (a - b) * F y else 0 := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> ring
      rw [hite, Finset.sum_ite_eq' Sx (roundAt x a), if_pos ha_Sx]

private lemma sum_lamL_const (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ)
    (Sx : Finset (V → ℤ))
    (hSx : Sx = Finset.filter (fun y => y ∈ DomZ g) (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L → (∀ c ∈ L, 0 ≤ c) →
      roundListSum g x L ≠ ⊤ →
      ∑ y ∈ Sx, lamL x L y * (1 : ℝ) = L.headD 0 - L.getLastD 0
  | [], hne, _, _, _ => False.elim (hne rfl)
  | [a], _, _, _, _ => by simp [lamL]
  | a :: b :: rest, _, hpw, h0, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨_, hpw'⟩
      have h0' : ∀ c ∈ b :: rest, 0 ≤ c := fun c hc => h0 c (List.mem_cons_of_mem a hc)
      have hne_top' : roundListSum g x (b :: rest) ≠ ⊤ := by
        intro htop
        apply hne_top
        simp [roundListSum, htop]
      rw [sum_lamL_mul g x Sx hSx (fun _ => 1) (a :: b :: rest) hpw h0 hne_top]
      dsimp only
      rw [sum_lamL_const g x Sx hSx (b :: rest) (by simp) hpw' h0' hne_top']
      simp only [mul_one, List.headD_cons, List.getLastD_cons]
      ring

private lemma sum_lamL_coord (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ)
    (Sx : Finset (V → ℤ))
    (hSx : Sx = Finset.filter (fun y => y ∈ DomZ g) (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)) (v : V) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L → (∀ c ∈ L, 0 ≤ c) →
      roundListSum g x L ≠ ⊤ →
      (x v - (⌊x v⌋ : ℝ) ∈ L →
        ∑ y ∈ Sx, lamL x L y * (y v : ℝ) =
          (L.headD 0 - L.getLastD 0) * (⌊x v⌋ : ℝ) + ((x v - (⌊x v⌋ : ℝ)) - L.getLastD 0)) ∧
      ((∀ c ∈ L, c < x v - (⌊x v⌋ : ℝ)) →
        ∑ y ∈ Sx, lamL x L y * (y v : ℝ) =
          (L.headD 0 - L.getLastD 0) * ((⌊x v⌋ : ℝ) + 1)) := by
  intro L hne hpw h0 hne_top
  induction L with
  | nil => exact False.elim (hne rfl)
  | cons a tail ih =>
    cases tail with
    | nil =>
      refine ⟨fun hmem => ?_, fun hlt => ?_⟩
      · simp only [List.mem_singleton] at hmem
        simp [lamL, ← hmem]
      · simp [lamL]
    | cons b rest =>
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have h0' : ∀ c ∈ b :: rest, 0 ≤ c := fun c hc => h0 c (List.mem_cons_of_mem a hc)
      have hne_top' : roundListSum g x (b :: rest) ≠ ⊤ :=
        fun htop => hne_top (by simp [roundListSum, htop])
      rcases ih (by simp) hpw' h0' hne_top' with ⟨ih_mem, ih_lt⟩
      rw [sum_lamL_mul g x Sx hSx (fun y => (y v : ℝ)) (a :: b :: rest) hpw h0 hne_top]
      dsimp only
      refine ⟨fun hmem => ?_, fun hlt => ?_⟩
      · rcases List.mem_cons.mp hmem with h_eq | hmem'
        · have hlt' : ∀ c ∈ b :: rest, c < x v - (⌊x v⌋ : ℝ) := by
            intro c hc; rw [h_eq]; exact ha_gt c hc
          rw [ih_lt hlt']
          have hr_a : (roundAt x a v : ℝ) = (⌊x v⌋ : ℝ) + 1 := by
            dsimp only [roundAt, roundAt1D]
            rw [if_pos (le_of_eq h_eq.symm)]
            push_cast; ring
          rw [hr_a, h_eq]
          simp only [List.headD_cons, List.getLastD_cons]
          ring
        · rw [ih_mem hmem']
          have h_gt : x v - (⌊x v⌋ : ℝ) < a := ha_gt _ hmem'
          have hr_a : (roundAt x a v : ℝ) = (⌊x v⌋ : ℝ) := by
            dsimp only [roundAt, roundAt1D]
            rw [if_neg (not_le_of_gt h_gt)]
            push_cast; ring
          rw [hr_a]
          simp only [List.headD_cons, List.getLastD_cons]
          ring
      · have hlt' : ∀ c ∈ b :: rest, c < x v - (⌊x v⌋ : ℝ) :=
          fun c hc => hlt c (List.mem_cons_of_mem a hc)
        rw [ih_lt hlt']
        have ha_lt : a < x v - (⌊x v⌋ : ℝ) := hlt a List.mem_cons_self
        have hr_a : (roundAt x a v : ℝ) = (⌊x v⌋ : ℝ) + 1 := by
          dsimp only [roundAt, roundAt1D]
          rw [if_pos (le_of_lt ha_lt)]
          push_cast; ring
        rw [hr_a]
        simp only [List.headD_cons, List.getLastD_cons]
        ring

private lemma sum_lamL_g (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ)
    (Sx : Finset (V → ℤ))
    (hSx : Sx = Finset.filter (fun y => y ∈ DomZ g) (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L → (∀ c ∈ L, 0 ≤ c) →
      roundListSum g x L ≠ ⊤ →
      ((∑ y ∈ Sx, lamL x L y * (g y).untopD 0 : ℝ) : WithTop ℝ) = roundListSum g x L
  | [], _, _, _ => by simp [lamL, roundListSum]
  | [_], _, _, _ => by simp [lamL, roundListSum]
  | a :: b :: rest, hpw, h0, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab_lt : b < a := ha_gt b List.mem_cons_self
      have hab_ne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hab_lt)
      have h0' : ∀ c ∈ b :: rest, 0 ≤ c := fun c hc => h0 c (List.mem_cons_of_mem a hc)
      have hne_top' : roundListSum g x (b :: rest) ≠ ⊤ :=
        fun htop => hne_top (by simp [roundListSum, htop])
      have hhead_ne_top : PosScalarMul (a - b) (g (roundAt x a)) ≠ ⊤ :=
        fun htop => hne_top (by simp [roundListSum, htop])
      have hdom_a : g (roundAt x a) ≠ ⊤ := by
        intro htop
        apply hhead_ne_top
        simp [PosScalarMul, htop, hab_ne]
      rw [sum_lamL_mul g x Sx hSx (fun y => (g y).untopD 0) (a :: b :: rest) hpw h0 hne_top]
      dsimp only
      rw [WithTop.coe_add, sum_lamL_g g x Sx hSx (b :: rest) hpw' h0' hne_top']
      simp only [roundListSum]
      congr 1
      lift g (roundAt x a) to ℝ using hdom_a with r hr
      simp [PosScalarMul]

private lemma convexClosureVal_le_roundListSum (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g)
    (x : V → ℝ) (L : List ℝ) (hne : L ≠ []) (hpw : List.Pairwise (· > ·) L)
    (h0 : ∀ c ∈ L, 0 ≤ c) (hhead : L.headD 0 = 1) (hlast : L.getLastD 0 = 0)
    (hmem : ∀ v : V, x v - (⌊x v⌋ : ℝ) ∈ L) :
    ConvexClosureVal g x ≤ roundListSum g x L := by
  by_cases htop : roundListSum g x L = ⊤
  · rw [htop]; exact le_top
  · let Sx := Finset.filter (fun y => y ∈ DomZ g)
      (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)
    have hIC : ConvexClosureVal g x = ConvexClosureValOn g Sx x := sbf_trf_imp_ic g hg x
    rw [hIC]
    unfold ConvexClosureValOn
    rw [← sum_lamL_g g x Sx rfl L hpw h0 htop]
    apply csInf_le (bddBelow_convexClosureValOn g Sx x)
    refine ⟨lamL x L, ?_, ?_, ?_, ?_, rfl⟩
    · intro y _
      exact lamL_nonneg x L hpw y
    · have hsum := sum_lamL_const g x Sx rfl L hne hpw h0 htop
      simp only [mul_one, hhead, hlast, sub_zero] at hsum
      exact hsum
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · intro v
      have hcoord := (sum_lamL_coord g x Sx rfl v L hne hpw h0 htop).1 (hmem v)
      rw [hhead, hlast] at hcoord
      linarith


private lemma scalarWithTop_mono {c : ℝ} (hc : 0 ≤ c) {z w : WithTop ℝ} (h : z ≤ w) :
    DiscreteConvex.MConvexSetsB.ScalarWithTop c z ≤ DiscreteConvex.MConvexSetsB.ScalarWithTop c w := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · cases z <;> cases w <;> simp [DiscreteConvex.MConvexSetsB.ScalarWithTop]
  · cases w with
    | top =>
      cases z <;> simp [DiscreteConvex.MConvexSetsB.ScalarWithTop, ne_of_gt hc_pos]
    | coe rw =>
      cases z with
      | top => exact False.elim (WithTop.not_top_le_coe rw h)
      | coe rz =>
        rw [WithTop.coe_le_coe] at h
        dsimp [DiscreteConvex.MConvexSetsB.ScalarWithTop]
        exact_mod_cast mul_le_mul_of_nonneg_left h hc

private lemma jensen_isConvexWithTop (f : (V → ℝ) → WithTop ℝ)
    (hf : DiscreteConvex.MConvexSetsB.IsConvexWithTop f)
    (S : Finset (V → ℤ)) :
    ∀ (lam : (V → ℤ) → ℝ) (z : (V → ℤ) → (V → ℝ)) (val : (V → ℤ) → ℝ),
      (∀ y ∈ S, 0 ≤ lam y) →
      (∑ y ∈ S, lam y = 1) →
      (∀ y ∈ S, f (z y) ≤ (val y : WithTop ℝ)) →
      f (fun v => ∑ y ∈ S, lam y * z y v) ≤ ((∑ y ∈ S, lam y * val y : ℝ) : WithTop ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro lam _ _ _ h1 _
    simp at h1
  | @insert a S' ha ih =>
    intro lam z val h0 h1 hle
    have hsum_ins : lam a + ∑ y ∈ S', lam y = 1 := by
      rw [← Finset.sum_insert ha]
      exact h1
    have ha0 : 0 ≤ lam a := h0 a (Finset.mem_insert_self a S')
    have hS0 : ∀ y ∈ S', 0 ≤ lam y := fun y hy => h0 y (Finset.mem_insert_of_mem hy)
    have hsum_nonneg : 0 ≤ ∑ y ∈ S', lam y := Finset.sum_nonneg hS0
    rcases eq_or_lt_of_le hsum_nonneg with hsum_zero | hsum_pos
    · have hlam_zero : ∀ y ∈ S', lam y = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hS0).mp hsum_zero.symm
      have ha1 : lam a = 1 := by linarith
      have hpt : (fun v => ∑ y ∈ insert a S', lam y * z y v) = z a := by
        ext v
        rw [Finset.sum_insert ha, ha1, one_mul]
        have h0' : ∑ y ∈ S', lam y * z y v = 0 :=
          Finset.sum_eq_zero (fun y hy => by rw [hlam_zero y hy, zero_mul])
        linarith
      have hval : ∑ y ∈ insert a S', lam y * val y = val a := by
        rw [Finset.sum_insert ha, ha1, one_mul]
        have h0' : ∑ y ∈ S', lam y * val y = 0 :=
          Finset.sum_eq_zero (fun y hy => by rw [hlam_zero y hy, zero_mul])
        linarith
      rw [hpt, hval]
      exact hle a (Finset.mem_insert_self a S')
    · let s := ∑ y ∈ S', lam y
      have hs_pos : 0 < s := hsum_pos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      let lam' : (V → ℤ) → ℝ := fun y => lam y / s
      have h0' : ∀ y ∈ S', 0 ≤ lam' y := fun y hy => div_nonneg (hS0 y hy) (le_of_lt hs_pos)
      have h1' : ∑ y ∈ S', lam' y = 1 := by
        dsimp [lam']
        rw [← Finset.sum_div]
        exact div_self hs_ne
      have hle' : ∀ y ∈ S', f (z y) ≤ (val y : WithTop ℝ) :=
        fun y hy => hle y (Finset.mem_insert_of_mem hy)
      have ih_step := ih lam' z val h0' h1' hle'
      let x' : V → ℝ := fun v => ∑ y ∈ S', lam' y * z y v
      have hcomb : (fun v => ∑ y ∈ insert a S', lam y * z y v) =
          (fun v => lam a * z a v + (1 - lam a) * x' v) := by
        ext v
        rw [Finset.sum_insert ha]
        have h1s : 1 - lam a = s := by linarith
        rw [h1s]
        congr 1
        dsimp [x', lam']
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        field_simp [hs_ne]
      rw [hcomb]
      have ha_le1 : lam a ≤ 1 := by linarith
      have hconv := hf (z a) x' (lam a) ha0 ha_le1
      have hsc1 := scalarWithTop_mono ha0 (hle a (Finset.mem_insert_self a S'))
      have hsc2 := scalarWithTop_mono (sub_nonneg.mpr ha_le1) ih_step
      refine hconv.trans ((add_le_add hsc1 hsc2).trans_eq ?_)
      dsimp only [DiscreteConvex.MConvexSetsB.ScalarWithTop]
      rw [← WithTop.coe_add, Finset.sum_insert ha]
      congr 1
      have h1s : 1 - lam a = s := by linarith
      rw [h1s]
      congr 1
      dsimp [lam']
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      field_simp [hs_ne]

private lemma domZ_inf {g : (V → ℤ) → WithTop ℝ} (hSBF : SBF g) {y₁ y₂ : V → ℤ}
    (hy₁ : y₁ ∈ DomZ g) (hy₂ : y₂ ∈ DomZ g) : y₁ ⊓ y₂ ∈ DomZ g := by
  intro htop
  have hle := hSBF y₁ y₂
  rw [htop, add_top] at hle
  have hsum_top : g y₁ + g y₂ = ⊤ := top_le_iff.mp hle
  rcases WithTop.add_eq_top.mp hsum_top with h1 | h2
  · exact hy₁ h1
  · exact hy₂ h2

private lemma floor_mem_domZ (g : (V → ℤ) → WithTop ℝ) (hSBF : SBF g) (x : V → ℝ)
    (Sx : Finset (V → ℤ))
    (hSx : Sx = Finset.filter (fun y => y ∈ DomZ g) (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x))
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ Sx, 0 ≤ lam y) (h1 : ∑ y ∈ Sx, lam y = 1)
    (hbary : ∀ v : V, ∑ y ∈ Sx, lam y * (y v : ℝ) = x v) :
    (fun v => ⌊x v⌋) ∈ DomZ g := by
  have hne : Sx.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at h1
    norm_num at h1
  have hinf_dom : Sx.inf' hne id ∈ DomZ g := by
    refine Finset.inf'_induction hne id (fun _ ha _ hb => domZ_inf hSBF ha hb) ?_
    intro y hy
    rw [hSx, Finset.mem_filter] at hy
    exact hy.2
  have hinf_eq : Sx.inf' hne id = (fun v => ⌊x v⌋) := by
    ext v
    have hle_fl : (fun u => ⌊x u⌋) ≤ Sx.inf' hne id := by
      rw [Finset.le_inf'_iff]
      intro y hy
      rw [hSx, Finset.mem_filter, DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset,
        Fintype.mem_piFinset] at hy
      intro u
      exact (Finset.mem_Icc.mp (hy.1 u)).1
    have hge_v : ⌊x v⌋ ≤ (Sx.inf' hne id) v := hle_fl v
    by_contra hne_v
    have hgt_v : ⌊x v⌋ + 1 ≤ (Sx.inf' hne id) v := by omega
    have hy_ge : ∀ y ∈ Sx, ((⌊x v⌋ : ℝ) + 1) ≤ (y v : ℝ) := by
      intro y hy
      have hiy : (Sx.inf' hne id) v ≤ y v := (Finset.inf'_le id hy) v
      have : ⌊x v⌋ + 1 ≤ y v := le_trans hgt_v hiy
      exact_mod_cast this
    have hsum_ge : (⌊x v⌋ : ℝ) + 1 ≤ ∑ y ∈ Sx, lam y * (y v : ℝ) := by
      calc (⌊x v⌋ : ℝ) + 1
        _ = (∑ y ∈ Sx, lam y) * ((⌊x v⌋ : ℝ) + 1) := by rw [h1, one_mul]
        _ = ∑ y ∈ Sx, lam y * ((⌊x v⌋ : ℝ) + 1) := Finset.sum_mul Sx lam _
        _ ≤ ∑ y ∈ Sx, lam y * (y v : ℝ) :=
            Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hy_ge y hy) (h0 y hy))
    rw [hbary v] at hsum_ge
    linarith [Int.lt_floor_add_one (x v)]
  rw [← hinf_eq]
  exact hinf_dom

private lemma posScalarMul_shift_cancel {d c₀ : ℝ} (hd : d ≠ 0) (w : WithTop ℝ) :
    PosScalarMul d (w + ((-c₀ : ℝ) : WithTop ℝ)) + ((d * c₀ : ℝ) : WithTop ℝ) =
      PosScalarMul d w := by
  cases w with
  | top =>
    simp [PosScalarMul, hd]
  | coe r =>
    change PosScalarMul d ((r : WithTop ℝ) + ((-c₀ : ℝ) : WithTop ℝ)) + ((d * c₀ : ℝ) : WithTop ℝ) =
      PosScalarMul d (r : WithTop ℝ)
    rw [← WithTop.coe_add]
    dsimp only [PosScalarMul]
    rw [← WithTop.coe_add]
    congr 1
    ring

private lemma lovaszList_shift_eq_roundListSum (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) (c₀ : ℝ) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L → L.getLastD 0 = 0 →
      lovaszList (fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ))
          (fun v => x v - (⌊x v⌋ : ℝ)) L +
        (((L.headD 0 - L.getLastD 0) * c₀ : ℝ) : WithTop ℝ) =
        roundListSum g x L
  | [], hne, _, _ => False.elim (hne rfl)
  | [a], _, _, hlast => by
      change a = 0 at hlast
      subst hlast
      simp [lovaszList, roundListSum, posScalarMul_zero]
  | a :: b :: rest, _, hpw, hlast => by
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab_ne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr (ha_gt b List.mem_cons_self))
      have hlast' : (b :: rest).getLastD 0 = 0 := hlast
      have ih := lovaszList_shift_eq_roundListSum g x c₀ (b :: rest) (by simp) hpw' hlast'
      change PosScalarMul (a - b)
          (g (fun v => ⌊x v⌋ + if v ∈ Finset.univ.filter (fun v => a ≤ x v - (⌊x v⌋ : ℝ)) then (1 : ℤ) else 0) +
            ((-c₀ : ℝ) : WithTop ℝ)) +
        lovaszList (fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ))
          (fun v => x v - (⌊x v⌋ : ℝ)) (b :: rest) +
        (((a - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ) =
        PosScalarMul (a - b) (g (roundAt x a)) + roundListSum g x (b :: rest)
      have hset : (fun v => ⌊x v⌋ + if v ∈ Finset.univ.filter (fun v => a ≤ x v - (⌊x v⌋ : ℝ)) then (1 : ℤ) else 0) =
          roundAt x a := by
        ext v
        dsimp only [roundAt, roundAt1D]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hset]
      have hdecomp' : (((a - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ) =
          (((a - b) * c₀ : ℝ) : WithTop ℝ) + (((b - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
      rw [hdecomp']
      have ih' : lovaszList (fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ))
            (fun v => x v - (⌊x v⌋ : ℝ)) (b :: rest) +
          (((b - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ) =
          roundListSum g x (b :: rest) := ih
      calc (PosScalarMul (a - b) (g (roundAt x a) + ((-c₀ : ℝ) : WithTop ℝ)) +
            lovaszList (fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ))
              (fun v => x v - (⌊x v⌋ : ℝ)) (b :: rest)) +
          ((((a - b) * c₀ : ℝ) : WithTop ℝ) + (((b - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ))
        _ = (PosScalarMul (a - b) (g (roundAt x a) + ((-c₀ : ℝ) : WithTop ℝ)) +
              (((a - b) * c₀ : ℝ) : WithTop ℝ)) +
            (lovaszList (fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ))
              (fun v => x v - (⌊x v⌋ : ℝ)) (b :: rest) +
              (((b - (b :: rest).getLastD 0) * c₀ : ℝ) : WithTop ℝ)) := by ac_rfl
        _ = PosScalarMul (a - b) (g (roundAt x a)) + roundListSum g x (b :: rest) := by
            rw [posScalarMul_shift_cancel hab_ne, ih']

private lemma coe_untopD_of_ne_top {w : WithTop ℝ} (hw : w ≠ ⊤) :
    ((w.untopD 0 : ℝ) : WithTop ℝ) = w := by
  lift w to ℝ using hw with r
  rfl

private lemma roundListSum_le_convexClosureVal [Nonempty V] (g : (V → ℤ) → WithTop ℝ)
    (hg : SBF g ∧ TRF g) (x : V → ℝ) (L : List ℝ) (hne : L ≠ [])
    (hpw : List.Pairwise (· > ·) L) (hhead : L.headD 0 = 1) (hlast : L.getLastD 0 = 0)
    (hmem : ∀ v : V, x v - (⌊x v⌋ : ℝ) ∈ L) :
    roundListSum g x L ≤ ConvexClosureVal g x := by
  let Sx := Finset.filter (fun y => y ∈ DomZ g)
    (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)
  have hIC : ConvexClosureVal g x = ConvexClosureValOn g Sx x := sbf_trf_imp_ic g hg x
  rw [hIC]
  unfold ConvexClosureValOn
  let A := {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ Sx, 0 ≤ lam y) ∧ (∑ y ∈ Sx, lam y = 1) ∧ (∀ y ∈ Sx, y ∈ DomZ g) ∧
    (∀ v, ∑ y ∈ Sx, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ Sx, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)}
  rcases A.eq_empty_or_nonempty with hA_empty | hA_ne
  · change roundListSum g x L ≤ sInf A
    rw [hA_empty, WithTop.sInf_empty]
    exact le_top
  apply le_csInf hA_ne
  rintro val ⟨lam, h0, h1, hdom, hbary, rfl⟩
  have hfl_dom : (fun v => ⌊x v⌋) ∈ DomZ g := floor_mem_domZ g hg.1 x Sx rfl lam h0 h1 hbary
  let c₀ : ℝ := (g (fun v => ⌊x v⌋)).untopD 0
  have hc₀ : g (fun v => ⌊x v⌋) = (c₀ : WithTop ℝ) := (coe_untopD_of_ne_top hfl_dom).symm
  let rho : Finset V → WithTop ℝ :=
    fun Y => g (fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0) + ((-c₀ : ℝ) : WithTop ℝ)
  have hrho0 : rho ∅ = 0 := by
    change g (fun v => ⌊x v⌋ + if v ∈ (∅ : Finset V) then (1 : ℤ) else 0) + ((-c₀ : ℝ) : WithTop ℝ) = 0
    have h0' : (fun v => ⌊x v⌋ + if v ∈ (∅ : Finset V) then (1 : ℤ) else 0) = (fun v => ⌊x v⌋) := by
      ext v; simp
    rw [h0', hc₀, ← WithTop.coe_add]
    simp
  have hrhoV : rho Finset.univ ≠ ⊤ := by
    change g (fun v => ⌊x v⌋ + if v ∈ (Finset.univ : Finset V) then (1 : ℤ) else 0) + ((-c₀ : ℝ) : WithTop ℝ) ≠ ⊤
    rcases hg.2 with ⟨r, hr⟩
    have huniv : (fun v => ⌊x v⌋ + if v ∈ (Finset.univ : Finset V) then (1 : ℤ) else 0) =
        (fun v => ⌊x v⌋) + 1 := by
      ext v; simp [Pi.add_apply]
    rw [huniv, hr, hc₀, ← WithTop.coe_add, ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  have hrho_sub : ∀ X Y : Finset V, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y) := by
    intro X Y
    dsimp [rho]
    let pX : V → ℤ := fun v => ⌊x v⌋ + if v ∈ X then 1 else 0
    let pY : V → ℤ := fun v => ⌊x v⌋ + if v ∈ Y then 1 else 0
    have hsup : (fun v => ⌊x v⌋ + if v ∈ X ∪ Y then (1 : ℤ) else 0) = pX ⊔ pY := by
      ext v
      dsimp [pX, pY]
      by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hx, hy]
    have hinf : (fun v => ⌊x v⌋ + if v ∈ X ∩ Y then (1 : ℤ) else 0) = pX ⊓ pY := by
      ext v
      dsimp [pX, pY]
      by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hx, hy]
    rw [hsup, hinf]
    calc (g (pX ⊔ pY) + ((-c₀ : ℝ) : WithTop ℝ)) + (g (pX ⊓ pY) + ((-c₀ : ℝ) : WithTop ℝ))
      _ = (g (pX ⊔ pY) + g (pX ⊓ pY)) + (((-c₀ : ℝ) : WithTop ℝ) + ((-c₀ : ℝ) : WithTop ℝ)) := by ac_rfl
      _ ≤ (g pX + g pY) + (((-c₀ : ℝ) : WithTop ℝ) + ((-c₀ : ℝ) : WithTop ℝ)) :=
          add_le_add (hg.1 pX pY) le_rfl
      _ = (g pX + ((-c₀ : ℝ) : WithTop ℝ)) + (g pY + ((-c₀ : ℝ) : WithTop ℝ)) := by ac_rfl
  have hrho_sbf : SubmodularSetFunction rho := ⟨hrho0, hrhoV, hrho_sub⟩
  have hconv : DiscreteConvex.MConvexSetsB.IsConvexWithTop (DiscreteConvex.MConvexSetsB.LovaszExtension rho) :=
    (DiscreteConvex.MConvexSetsB.lovasz_convex_iff_submodular rho hrho0 hrhoV).mp hrho_sub
  let z : (V → ℤ) → (V → ℝ) := fun y v => (y v : ℝ) - (⌊x v⌋ : ℝ)
  have hz_val : ∀ y ∈ Sx,
      DiscreteConvex.MConvexSetsB.LovaszExtension rho (z y) ≤ (((g y).untopD 0 - c₀ : ℝ) : WithTop ℝ) := by
    intro y hy
    have hy_nb : y ∈ DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x :=
      (Finset.mem_filter.mp hy).1
    have hy_dom : y ∈ DomZ g := (Finset.mem_filter.mp hy).2
    have hpw10 : List.Pairwise (· > ·) ([1, 0] : List ℝ) := by simp
    have hmem10 : ∀ v : V, z y v ∈ ([1, 0] : List ℝ) := by
      intro v
      simp only [DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset,
        Fintype.mem_piFinset, Finset.mem_Icc] at hy_nb
      have hv_bounds := hy_nb v
      have hceil : ⌈x v⌉ ≤ ⌊x v⌋ + 1 := Int.ceil_le_floor_add_one (x v)
      have h01 : y v = ⌊x v⌋ ∨ y v = ⌊x v⌋ + 1 := by omega
      dsimp [z]
      rcases h01 with h_eq0 | h_eq1
      · simp [h_eq0]
      · rw [h_eq1]; push_cast; simp
    rw [lovasz_eq_lovaszList_of_mem rho hrho_sbf (z y) [1, 0] hpw10 hmem10]
    simp only [lovaszList, sub_zero, posScalarMul_zero, add_zero]
    have h1' : PosScalarMul 1 (rho (Finset.univ.filter (fun v => 1 ≤ z y v))) =
        rho (Finset.univ.filter (fun v => 1 ≤ z y v)) := by
      cases rho (Finset.univ.filter (fun v => 1 ≤ z y v)) <;> simp [PosScalarMul]
    rw [h1']
    have hy_eq : (fun v => ⌊x v⌋ + if v ∈ Finset.univ.filter (fun v => 1 ≤ z y v) then (1 : ℤ) else 0) = y := by
      ext v
      simp only [DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset,
        Fintype.mem_piFinset, Finset.mem_Icc] at hy_nb
      have hv_bounds := hy_nb v
      have hceil : ⌈x v⌉ ≤ ⌊x v⌋ + 1 := Int.ceil_le_floor_add_one (x v)
      have h01 : y v = ⌊x v⌋ ∨ y v = ⌊x v⌋ + 1 := by omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, z]
      rcases h01 with h_eq0 | h_eq1
      · rw [h_eq0]; simp
      · rw [h_eq1]; push_cast; simp
    change g (fun v => ⌊x v⌋ + if v ∈ Finset.univ.filter (fun v => 1 ≤ z y v) then (1 : ℤ) else 0) +
        ((-c₀ : ℝ) : WithTop ℝ) ≤ (((g y).untopD 0 - c₀ : ℝ) : WithTop ℝ)
    rw [hy_eq, ← coe_untopD_of_ne_top hy_dom, ← WithTop.coe_add]
    exact le_of_eq (by congr 1)
  have hjensen := jensen_isConvexWithTop (DiscreteConvex.MConvexSetsB.LovaszExtension rho) hconv
    Sx lam z (fun y => (g y).untopD 0 - c₀) h0 h1 hz_val
  have hcomb_x : (fun v => ∑ y ∈ Sx, lam y * z y v) = (fun v => x v - (⌊x v⌋ : ℝ)) := by
    ext v
    change ∑ y ∈ Sx, lam y * ((y v : ℝ) - (⌊x v⌋ : ℝ)) = x v - (⌊x v⌋ : ℝ)
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbary v, h1, one_mul]
  rw [hcomb_x, lovasz_eq_lovaszList_of_mem rho hrho_sbf (fun v => x v - (⌊x v⌋ : ℝ)) L hpw hmem] at hjensen
  have hshift := lovaszList_shift_eq_roundListSum g x c₀ L hne hpw hlast
  rw [hhead, hlast, sub_zero, one_mul] at hshift
  rw [← hshift]
  refine (add_le_add hjensen (le_rfl : (c₀ : WithTop ℝ) ≤ (c₀ : WithTop ℝ))).trans_eq ?_
  rw [← WithTop.coe_add]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  ring

private lemma getLastD_eq_getLast_of_ne_nil :
    ∀ (L : List ℝ) (hne : L ≠ []), L.getLastD 0 = L.getLast hne
  | [], hne => False.elim (hne rfl)
  | [a], _ => rfl
  | a :: b :: rest, _ => getLastD_eq_getLast_of_ne_nil (b :: rest) (by simp)

theorem solution (g : (V → ℤ) → WithTop ℝ)
    (hg : SBF g ∧ TRF g) (hpoly : IsPolyhedralConvex (fun p => ConvexClosureVal g p)) :
    SBFR (fun p => ConvexClosureVal g p) ∧ TRFR (fun p => ConvexClosureVal g p) := by
  have _ := hpoly
  constructor
  · intro p q
    rcases isEmpty_or_nonempty V with hEmpty | hNonempty
    · have hpq : p ⊔ q = p := Subsingleton.elim _ _
      have hqp : p ⊓ q = q := Subsingleton.elim _ _
      rw [hpq, hqp]
    · let S : Finset ℝ :=
        insert 1 (insert 0
          (Finset.univ.image (fun v => p v - (⌊p v⌋ : ℝ)) ∪
            Finset.univ.image (fun v => q v - (⌊q v⌋ : ℝ))))
      let L : List ℝ := S.sort (· ≥ ·)
      have h1_mem : (1 : ℝ) ∈ L :=
        (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_insert_self 1 _)
      have h0_mem : (0 : ℝ) ∈ L :=
        (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self 0 _))
      have hne : L ≠ [] := List.ne_nil_of_mem h1_mem
      have hpw : List.Pairwise (· > ·) L := pairwise_gt_sort S
      have hbounds : ∀ c ∈ L, 0 ≤ c ∧ c ≤ 1 := by
        intro c hc
        have hcS : c ∈ S := (Finset.mem_sort (· ≥ ·)).mp hc
        rcases Finset.mem_insert.mp hcS with rfl | hcS
        · exact ⟨by norm_num, by norm_num⟩
        · rcases Finset.mem_insert.mp hcS with rfl | hcS
          · exact ⟨by norm_num, by norm_num⟩
          · rcases Finset.mem_union.mp hcS with hcp | hcq
            · rcases Finset.mem_image.mp hcp with ⟨v, _, rfl⟩
              exact ⟨sub_nonneg.mpr (Int.floor_le (p v)),
                by linarith [Int.lt_floor_add_one (p v)]⟩
            · rcases Finset.mem_image.mp hcq with ⟨v, _, rfl⟩
              exact ⟨sub_nonneg.mpr (Int.floor_le (q v)),
                by linarith [Int.lt_floor_add_one (q v)]⟩
      have h0 : ∀ c ∈ L, 0 ≤ c := fun c hc => (hbounds c hc).1
      have hhead : L.headD 0 = 1 := by
        cases hL : L with
        | nil => exact False.elim (hne hL)
        | cons a rest =>
          simp only [List.headD_cons]
          have ha_mem : a ∈ L := by rw [hL]; exact List.mem_cons_self
          have ha_le1 : a ≤ 1 := (hbounds a ha_mem).2
          have h1_in : (1 : ℝ) ∈ a :: rest := by rw [← hL]; exact h1_mem
          rcases List.mem_cons.mp h1_in with rfl | h1_rest
          · rfl
          · rw [hL] at hpw
            have ha_gt1 : a > 1 := (List.pairwise_cons.mp hpw).1 1 h1_rest
            linarith
      have hlast : L.getLastD 0 = 0 := by
        have hlast_mem : L.getLast hne ∈ L := List.getLast_mem hne
        have hlast_eq : L.getLastD 0 = L.getLast hne := getLastD_eq_getLast_of_ne_nil L hne
        rw [hlast_eq]
        have hge0 : 0 ≤ L.getLast hne := (hbounds _ hlast_mem).1
        by_contra hne0
        have hgt0 : 0 < L.getLast hne := lt_of_le_of_ne hge0 (Ne.symm hne0)
        rw [List.mem_iff_getElem] at h0_mem
        rcases h0_mem with ⟨i, hi, hLi⟩
        have hlast_idx : L.getLast hne = L[L.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) (by omega)) :=
          List.getLast_eq_getElem hne
        by_cases hi_last : i = L.length - 1
        · subst hi_last
          rw [hlast_idx, hLi] at hgt0
          exact lt_irrefl 0 hgt0
        · have hi_lt : i < L.length - 1 := by omega
          rw [List.pairwise_iff_getElem] at hpw
          have hgt := hpw i (L.length - 1) hi (Nat.sub_lt (List.length_pos_of_ne_nil hne) (by omega)) hi_lt
          rw [hLi, ← hlast_idx] at hgt
          linarith
      have hmem_p : ∀ v : V, p v - (⌊p v⌋ : ℝ) ∈ L := by
        intro v
        rw [Finset.mem_sort]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))))
      have hmem_q : ∀ v : V, q v - (⌊q v⌋ : ℝ) ∈ L := by
        intro v
        rw [Finset.mem_sort]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))))
      have hmem_sup : ∀ v : V, (p ⊔ q) v - (⌊(p ⊔ q) v⌋ : ℝ) ∈ L := by
        intro v
        simp only [Pi.sup_apply]
        rcases max_choice (p v) (q v) with hmax | hmax <;> rw [hmax]
        · exact hmem_p v
        · exact hmem_q v
      have hmem_inf : ∀ v : V, (p ⊓ q) v - (⌊(p ⊓ q) v⌋ : ℝ) ∈ L := by
        intro v
        simp only [Pi.inf_apply]
        rcases min_choice (p v) (q v) with hmin | hmin <;> rw [hmin]
        · exact hmem_p v
        · exact hmem_q v
      have hle_sup := convexClosureVal_le_roundListSum g hg (p ⊔ q) L hne hpw h0 hhead hlast hmem_sup
      have hle_inf := convexClosureVal_le_roundListSum g hg (p ⊓ q) L hne hpw h0 hhead hlast hmem_inf
      have hge_p := roundListSum_le_convexClosureVal g hg p L hne hpw hhead hlast hmem_p
      have hge_q := roundListSum_le_convexClosureVal g hg q L hne hpw hhead hlast hmem_q
      have hsbf_L := roundListSum_sbf g hg.1 p q L hpw
      exact (add_le_add hle_sup hle_inf).trans (hsbf_L.trans (add_le_add hge_p hge_q))
  · rcases (DiscreteConvex.LConvexFunctionsB.lconvex_closure_basic_properties g hg).2 with ⟨r, _, hr⟩
    exact ⟨r, fun p alpha => hr p alpha⟩
