-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibrium.m_natural_concave_iff_neg_si
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:46:29.811595+00:00
-- url     : https://prove2.me/submissions/af066057-2e00-4f8d-84fd-03e9df044f55

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegSI
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegUtil
import Theorems.Thm_DiscreteConvex_MConvexFunctions_mnat_convex_iff_exchange_axiom
import Theorems.Thm_DiscreteConvex_MConvexFunctionsB_exchange_axiom_iff_sequential_improvement

open Classical
open scoped Pointwise
open DiscreteConvex.EconomicEquilibrium

set_option linter.unusedSectionVars false

namespace Pdeff9a30

variable {K : Type*} [Fintype K] [DecidableEq K]

@[simp] lemma negUtil_bot : NegUtil (⊥ : WithBot ℝ) = ⊤ := rfl

@[simp] lemma negUtil_coe (r : ℝ) : NegUtil ((r : ℝ) : WithBot ℝ) = ((-r : ℝ) : WithTop ℝ) := rfl

lemma negUtil_eq_top {v : WithBot ℝ} : NegUtil v = ⊤ ↔ v = ⊥ := by
  induction v using WithBot.recBotCoe with
  | bot => simp
  | coe r => simp

lemma negUtil_ne_top {v : WithBot ℝ} : NegUtil v ≠ ⊤ ↔ v ≠ ⊥ :=
  negUtil_eq_top.not

lemma negUtil_add (a b : WithBot ℝ) : NegUtil (a + b) = NegUtil a + NegUtil b := by
  induction a using WithBot.recBotCoe with
  | bot => rfl
  | coe r =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot, negUtil_bot, negUtil_coe, WithTop.add_top]
    | coe s =>
      rw [← WithBot.coe_add, negUtil_coe, negUtil_coe, negUtil_coe, ← WithTop.coe_add]
      congr 1
      ring

lemma negUtil_le_iff {a b : WithBot ℝ} : NegUtil a ≤ NegUtil b ↔ b ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => simp
    | coe s => simp
  | coe r =>
    induction b using WithBot.recBotCoe with
    | bot => simp
    | coe s =>
      rw [negUtil_coe, negUtil_coe, WithTop.coe_le_coe, WithBot.coe_le_coe]
      exact neg_le_neg_iff

lemma negUtil_lt_iff {a b : WithBot ℝ} : NegUtil a < NegUtil b ↔ b < a :=
  lt_iff_lt_of_le_iff_le negUtil_le_iff

lemma negUtil_max (a b : WithBot ℝ) : NegUtil (max a b) = min (NegUtil a) (NegUtil b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_right (negUtil_le_iff.mpr h)]
  · rw [max_eq_left h, min_eq_left (negUtil_le_iff.mpr h)]

lemma negUtil_sup {α : Type*} (s : Finset α) (g : α → WithBot ℝ) :
    NegUtil (s.sup g) = s.inf (fun i => NegUtil (g i)) := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sup_cons, Finset.inf_cons]
    change NegUtil (max (g a) (s.sup g)) = min (NegUtil (g a)) (s.inf (fun i => NegUtil (g i)))
    rw [negUtil_max, ih]

lemma domZ_negUtil (U : (K → ℤ) → WithBot ℝ) (x : K → ℤ) :
    x ∈ DiscreteConvex.MConvexFunctions.DomZ (fun z => NegUtil (U z)) ↔ x ∈ UDom U := by
  simp [DiscreteConvex.MConvexFunctions.DomZ, UDom, negUtil_ne_top]

lemma mnatConcave_iff_mnatExchange (U : (K → ℤ) → WithBot ℝ) (hU : (UDom U).Nonempty) :
    MNaturalConcave U ↔
      DiscreteConvex.MConvexFunctions.MNatExchangeAxiom (fun z => NegUtil (U z)) := by
  refine ⟨fun ⟨_, h⟩ x hx y hy i hi => ?_, fun h => ⟨hU, fun x hx y hy i hi => ?_⟩⟩
  · have hx' : x ∈ UDom U := (domZ_negUtil U x).mp hx
    have hy' : y ∈ UDom U := (domZ_negUtil U y).mp hy
    have hxy := h x hx' y hy' i hi
    have hle := negUtil_le_iff.mpr hxy
    rw [negUtil_add, negUtil_max, negUtil_add, negUtil_sup] at hle
    simpa [negUtil_add] using hle
  · have hx' : x ∈ DiscreteConvex.MConvexFunctions.DomZ (fun z => NegUtil (U z)) :=
      (domZ_negUtil U x).mpr hx
    have hy' : y ∈ DiscreteConvex.MConvexFunctions.DomZ (fun z => NegUtil (U z)) :=
      (domZ_negUtil U y).mpr hy
    have hxy := h x hx' y hy' i hi
    rw [← negUtil_le_iff, negUtil_add, negUtil_max, negUtil_add, negUtil_sup]
    simpa [negUtil_add] using hxy

lemma linearWeight_negUtil (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) :
    DiscreteConvex.MConvexFunctionsB.LinearWeight (fun z => NegUtil (U z)) (fun k => -p k) x =
      NegUtil (PriceShift U p x) := by
  unfold DiscreteConvex.MConvexFunctionsB.LinearWeight PriceShift
  rw [negUtil_add, negUtil_coe]
  congr 2
  simp [neg_mul, Finset.sum_neg_distrib]

lemma bot_lt_priceShift_iff (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) :
    ⊥ < PriceShift U p x ↔ x ∈ DiscreteConvex.MConvexFunctionsB.DomZ (fun z => NegUtil (U z)) := by
  rw [bot_lt_iff_ne_bot]
  unfold PriceShift DiscreteConvex.MConvexFunctionsB.DomZ
  simp only [Set.mem_setOf_eq, negUtil_ne_top]
  induction U x using WithBot.recBotCoe with
  | bot => simp
  | coe r =>
    rw [← WithBot.coe_add]
    simp

lemma mnatSI_iff_negSI (U : (K → ℤ) → WithBot ℝ) :
    DiscreteConvex.MConvexFunctionsB.MNatSI (fun z => NegUtil (U z)) ↔ NegSI U := by
  let f : (K → ℤ) → WithTop ℝ := fun z => NegUtil (U z)
  have hchar : ∀ o : Option K,
      DiscreteConvex.MConvexFunctionsB.CharVecOpt o =
        DiscreteConvex.MConvexFunctions.CharVecOpt o := fun o => by
    cases o <;> rfl
  have hpos : ∀ x y : K → ℤ,
      DiscreteConvex.MConvexFunctionsB.SuppPos x y =
        DiscreteConvex.MConvexFunctions.SuppPos x y := fun _ _ => rfl
  have hneg : ∀ x y : K → ℤ,
      DiscreteConvex.MConvexFunctionsB.SuppNeg x y =
        DiscreteConvex.MConvexFunctions.SuppNeg x y := fun _ _ => rfl
  constructor
  · intro hSI p x y hbx hlt
    have hx : x ∈ DiscreteConvex.MConvexFunctionsB.DomZ f :=
      (bot_lt_priceShift_iff U p x).mp hbx
    have hy : y ∈ DiscreteConvex.MConvexFunctionsB.DomZ f :=
      (bot_lt_priceShift_iff U p y).mp (lt_trans hbx hlt)
    have hgt : DiscreteConvex.MConvexFunctionsB.LinearWeight f (fun k => -p k) x >
        DiscreteConvex.MConvexFunctionsB.LinearWeight f (fun k => -p k) y := by
      rw [gt_iff_lt, linearWeight_negUtil, linearWeight_negUtil, negUtil_lt_iff]
      exact hlt
    have H := hSI (fun k => -p k) x hx y hy hgt
    rw [gt_iff_lt, Finset.inf_lt_iff] at H
    obtain ⟨i, hi, Hi⟩ := H
    rw [Finset.inf_lt_iff] at Hi
    obtain ⟨j, hj, Hij⟩ := Hi
    rw [linearWeight_negUtil, linearWeight_negUtil, negUtil_lt_iff] at Hij
    simp only [hchar] at Hij
    rw [hpos, Finset.mem_insert, Finset.mem_image] at hi
    rw [hneg, Finset.mem_insert, Finset.mem_image] at hj
    refine ⟨i, ?_, j, ?_, Hij⟩
    · rcases hi with rfl | ⟨k, hk, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, rfl⟩
    · rcases hj with rfl | ⟨k, hk, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, rfl⟩
  · intro hNeg q x hx y hy hgt
    let p : K → ℝ := fun k => -q k
    have hqp : q = fun k => -p k := by funext k; simp [p]
    rw [hqp] at hgt ⊢
    rw [gt_iff_lt, linearWeight_negUtil, linearWeight_negUtil, negUtil_lt_iff] at hgt
    have hbx : ⊥ < PriceShift U p x := (bot_lt_priceShift_iff U p x).mpr hx
    obtain ⟨i, hi, j, hj, Hij⟩ := hNeg p x y hbx hgt
    rw [gt_iff_lt, Finset.inf_lt_iff]
    refine ⟨i, ?_, ?_⟩
    · rw [hpos, Finset.mem_insert, Finset.mem_image]
      rcases hi with rfl | ⟨k, hk, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, rfl⟩
    · rw [Finset.inf_lt_iff]
      refine ⟨j, ?_, ?_⟩
      · rw [hneg, Finset.mem_insert, Finset.mem_image]
        rcases hj with rfl | ⟨k, hk, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k, hk, rfl⟩
      · rw [linearWeight_negUtil, linearWeight_negUtil, negUtil_lt_iff]
        simpa [hchar] using Hij

end Pdeff9a30

open Pdeff9a30

theorem solution {K : Type*} [Fintype K] [DecidableEq K]
    (U : (K → ℤ) → WithBot ℝ) (hU : (UDom U).Nonempty) :
    MNaturalConcave U ↔ NegSI U := by
  let f : (K → ℤ) → WithTop ℝ := fun z => NegUtil (U z)
  obtain ⟨x0, hx0⟩ := hU
  have hf : (DiscreteConvex.MConvexFunctions.DomZ f).Nonempty :=
    ⟨x0, (domZ_negUtil U x0).mpr hx0⟩
  have hfB : (DiscreteConvex.MConvexFunctionsB.DomZ f).Nonempty := hf
  have h1 := mnatConcave_iff_mnatExchange U ⟨x0, hx0⟩
  have h2 := (DiscreteConvex.MConvexFunctions.mnat_convex_iff_exchange_axiom f hf).symm
  have h3 : DiscreteConvex.MConvexFunctions.MNaturalConvex f ↔
      DiscreteConvex.MConvexFunctionsB.MNaturalConvex f := Iff.rfl
  have h4 := (DiscreteConvex.MConvexFunctionsB.exchange_axiom_iff_sequential_improvement f hfB).2
  have h5 := mnatSI_iff_negSI U
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
