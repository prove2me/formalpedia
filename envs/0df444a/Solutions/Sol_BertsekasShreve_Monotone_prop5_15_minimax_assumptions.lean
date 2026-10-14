-- Prove2me | solution 1 for BertsekasShreve.Monotone.prop5_15_minimax_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:31:46.303895+00:00
-- url     : https://prove2.me/submissions/90090588-8d4a-412b-8404-783b3b3f6fa6

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

open Filter Topology

namespace BertsekasShreve.Monotone

open BertsekasShreve.FiniteHorizon

theorem mm_badd_of_ne_top {g z : EReal} (hg : g ≠ ⊤) (hz : z ≠ ⊤) : badd g z = g + z := by
  unfold badd
  rw [if_neg]
  rintro (h | h)
  · exact hg h
  · exact hz h

theorem mm_badd_coe (r : ℝ) (z : EReal) : badd (r : EReal) z = (r : EReal) + z := by
  unfold badd
  split_ifs with h
  · rcases h with h | h
    · exact absurd h (EReal.coe_ne_top r)
    · rw [h, EReal.coe_add_top]
  · rfl

theorem mm_badd_top (z : EReal) : badd ⊤ z = ⊤ := by
  unfold badd; simp

theorem mm_mul_add {α : ℝ} (hα : 0 < α) (r : ℝ) {z : EReal} (hz : z ≠ ⊥) :
    (α : EReal) * (z + (r : EReal)) = (α : EReal) * z + ((α * r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => exact absurd rfl hz
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hα, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring

theorem mm_mul_sub {α : ℝ} (hα : 0 < α) (r : ℝ) {z : EReal} (hz : z ≠ ⊤) :
    (α : EReal) * (z - (r : EReal)) = (α : EReal) * z - ((α * r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos hα, EReal.bot_sub]
  | top => exact absurd rfl hz
  | coe a => rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub]; congr 1; ring

theorem mm_mul_ne_top {α : ℝ} (hα : 0 < α) {z : EReal} (hz : z ≠ ⊤) : (α : EReal) * z ≠ ⊤ := by
  induction z using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hα]; exact bot_ne_top
  | top => exact absurd rfl hz
  | coe a => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _

theorem mm_contAt (r α : ℝ) (hα : 0 < α) (s : EReal) :
    ContinuousAt (fun z : EReal => (r : EReal) + (α : EReal) * z) s := by
  have h0 : (α : EReal) ≠ 0 := by exact_mod_cast hα.ne'
  have hmul : ContinuousAt (fun z : EReal => (α : EReal) * z) s := by
    have := EReal.continuousAt_mul (p := ((α : EReal), s)) (Or.inl h0) (Or.inl h0)
      (Or.inl (EReal.coe_ne_bot α)) (Or.inl (EReal.coe_ne_top α))
    exact ContinuousAt.comp (f := fun z : EReal => ((α : EReal), z)) this
      (continuousAt_const.prodMk continuousAt_id)
  have hadd := EReal.continuousAt_add (p := ((r : EReal), (α : EReal) * s))
    (Or.inl (EReal.coe_ne_top r)) (Or.inl (EReal.coe_ne_bot r))
  exact ContinuousAt.comp (f := fun z : EReal => ((r : EReal), (α : EReal) * z)) hadd
    (continuousAt_const.prodMk hmul)

theorem mm_elem {α : ℝ} (hα : 0 < α) (g : EReal) (hg : 0 ≤ g) (a : ℕ → EReal) :
    ⨆ k, badd g ((α : EReal) * a k) = badd g ((α : EReal) * ⨆ k, a k) := by
  induction g using EReal.rec with
  | bot => exact absurd hg (by simp)
  | top => simp [mm_badd_top]
  | coe r =>
    simp only [mm_badd_coe]
    have hmono : Monotone (fun z : EReal => (r : EReal) + (α : EReal) * z) := by
      intro a b hab
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hab (by exact_mod_cast hα.le))
    have hbot : (fun z : EReal => (r : EReal) + (α : EReal) * z) ⊥ = ⊥ := by
      simp only
      rw [EReal.coe_mul_bot_of_pos hα, EReal.add_bot]
    exact (Monotone.map_iSup_of_continuousAt (mm_contAt r α hα _) hmono hbot).symm

theorem prop5_15_core {S C W : Type*}
    (Wset : S → C → Set W) (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 α) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, g x u w ≤ 0) →
        m.AssumptionD ∧ m.AssumptionD2 α) := by
  have hα0 : (0 : EReal) ≤ (α : EReal) := by exact_mod_cast hα.le
  constructor
  · intro m hH hJ hW hg
    refine ⟨?_, ?_, ?_⟩
    · intro x u hu
      rw [hH, hJ]
      obtain ⟨w, hw⟩ := hW x u hu
      refine le_trans ?_ (le_iSup₂ (f := fun w (_ : w ∈ Wset x u) =>
        badd (g x u w) ((α : EReal) * (fun _ => (0 : EReal)) (f x u w))) w hw)
      simp only [mul_zero]
      unfold badd
      split_ifs
      · exact le_top
      · rw [add_zero]; exact hg x u hu w
    · intro Js hJs hmono x u hu
      have hmon : Monotone Js := monotone_nat_of_le_succ hmono
      have hL : (fun y => limUnder atTop (fun k => Js k y)) = fun y => ⨆ k, Js k y := by
        funext y
        exact (tendsto_atTop_iSup (fun a b hab => hmon hab y)).limUnder_eq
      have hHmon : Monotone (fun k => m.H x u (Js k)) :=
        fun a b hab => m.mono x u hu _ _ (hmon hab)
      rw [(tendsto_atTop_iSup hHmon).limUnder_eq, hL, hH]
      simp only [minimaxH]
      rw [iSup_comm]
      refine iSup_congr fun w => ?_
      rw [iSup_comm]
      refine iSup_congr fun hw => ?_
      exact mm_elem hα _ (hg x u hu w) _
    · refine ⟨hα, fun r hr J hJJ x u hu => ⟨?_, ?_⟩⟩
      · apply m.mono x u hu
        intro y
        exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)
      · rw [hH]
        simp only [minimaxH]
        refine iSup₂_le fun w hw => ?_
        have hJ0 : 0 ≤ J (f x u w) := by
          have := hJJ (f x u w); rw [hJ] at this; exact this
        have hJb : J (f x u w) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hJ0
        rw [mm_mul_add hα r hJb]
        calc badd (g x u w) ((α : EReal) * J (f x u w) + ((α * r : ℝ) : EReal))
            ≤ badd (g x u w) ((α : EReal) * J (f x u w)) + ((α * r : ℝ) : EReal) := by
              have hg0 := hg x u hu w
              by_cases ht : g x u w = ⊤
              · rw [ht, mm_badd_top, mm_badd_top, EReal.top_add_coe]
              · have hb : g x u w ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hg0
                rw [← EReal.coe_toReal ht hb, mm_badd_coe, mm_badd_coe, add_assoc]
          _ ≤ _ := add_le_add (le_iSup₂ (f := fun w (_ : w ∈ Wset x u) =>
                badd (g x u w) ((α : EReal) * J (f x u w))) w hw) le_rfl
  · intro m hH hJ hW hg
    refine ⟨?_, hα, fun r hr J hJJ x u hu => ⟨?_, ?_⟩⟩
    · intro x u hu
      rw [hH, hJ]
      simp only [minimaxH, mul_zero]
      refine iSup₂_le fun w hw => ?_
      have hgt : g x u w ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hg x u hu w)
      rw [mm_badd_of_ne_top hgt (by simp), add_zero]
      exact hg x u hu w
    · rw [hH]
      simp only [minimaxH]
      have hc1 : ((α * r : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hc2 : ((α * r : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      rw [EReal.sub_le_iff_le_add (Or.inl hc1) (Or.inl hc2)]
      refine iSup₂_le fun w hw => ?_
      have hJt : J (f x u w) ≠ ⊤ := by
        have := hJJ (f x u w); rw [hJ] at this
        exact ne_top_of_le_ne_top (by simp) this
      have hgt : g x u w ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hg x u hu w)
      have key : badd (g x u w) ((α : EReal) * (J (f x u w) - (r : EReal))) =
          badd (g x u w) ((α : EReal) * J (f x u w)) - ((α * r : ℝ) : EReal) := by
        rw [mm_mul_sub hα r hJt, mm_badd_of_ne_top hgt (mm_mul_ne_top hα hJt)]
        have h2 : (α : EReal) * J (f x u w) - ((α * r : ℝ) : EReal) ≠ ⊤ := by
          rw [← mm_mul_sub hα r hJt]
          apply mm_mul_ne_top hα
          refine ne_top_of_le_ne_top hJt ?_
          rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot r)) (Or.inl (EReal.coe_ne_top r))]
          exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)
        rw [mm_badd_of_ne_top hgt h2, sub_eq_add_neg, sub_eq_add_neg, add_assoc]
      have hle : badd (g x u w) ((α : EReal) * J (f x u w)) ≤
          badd (g x u w) ((α : EReal) * (J (f x u w) - (r : EReal))) + ((α * r : ℝ) : EReal) := by
        rw [key, ← EReal.sub_le_iff_le_add (Or.inl hc1) (Or.inl hc2)]
      exact hle.trans (add_le_add (le_iSup₂ (f := fun w (_ : w ∈ Wset x u) =>
        badd (g x u w) ((α : EReal) * (J (f x u w) - (r : EReal)))) w hw) le_rfl)
    · apply m.mono x u hu
      intro y
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot r)) (Or.inl (EReal.coe_ne_top r))]
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)

end BertsekasShreve.Monotone

open BertsekasShreve.Monotone


theorem solution {S C W : Type*}
    (Wset : S → C → Set W) (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 α) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, g x u w ≤ 0) →
        m.AssumptionD ∧ m.AssumptionD2 α) := by
  exact prop5_15_core Wset g f α hα
