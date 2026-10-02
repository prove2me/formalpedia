-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.integer_biconjugate_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:38:44.354154+00:00
-- url     : https://prove2.me/submissions/312d46ea-e201-4762-8756-d4a7cea8a7d5

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SubdifferentialZ
import Definitions.Def_DiscreteConvex_ConjugacyDuality_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDuality_IsIntegerValued

set_option autoImplicit false

namespace DiscreteConvex.ConjugacyDuality

lemma ib7d_toE_real (s : ℝ) : ToEReal ((s : ℝ) : WithTop ℝ) = ((s : ℝ) : EReal) := rfl

lemma ib7d_toE_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

lemma ib7d_fromE_real (s : ℝ) : FromEReal ((s : ℝ) : EReal) = ((s : ℝ) : WithTop ℝ) := rfl

lemma ib7d_toE_fromE (v : EReal) (hv : v ≠ ⊥) : ToEReal (FromEReal v) = v := by
  induction v using EReal.rec with
  | bot => exact absurd rfl hv
  | coe s => rfl
  | top => rfl

end DiscreteConvex.ConjugacyDuality

open DiscreteConvex.ConjugacyDuality in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : IsIntegerValued f) (x : V → ℤ) (hx : x ∈ DomZ f)
    (hne : (SubdifferentialZ f x).Nonempty) :
    ConvexConjugate (ConvexConjugate f) x = f x := by
  obtain ⟨p, hp⟩ := hne
  have hx' : f x ≠ ⊤ := hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx'
  -- hr : ↑r = f x
  set a : ℝ := ∑ i, (p i : ℝ) * (x i : ℝ) with ha
  -- f• p = a - r
  have hS1 : sSup {v : EReal | ∃ y : V → ℤ,
      v = ((∑ i, (p i : ℝ) * (y i : ℝ) : ℝ) : EReal) - ToEReal (f y)} = ((a - r : ℝ) : EReal) := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨y, rfl⟩
      have hpy := hp y
      by_cases hft : f y = ⊤
      · rw [hft, ib7d_toE_top, EReal.sub_top]; exact bot_le
      · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hft
        rw [← hs, ib7d_toE_real, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        rw [← hs, ← hr] at hpy
        have h2 := WithTop.coe_le_coe.mp (by simpa only [← WithTop.coe_add] using hpy)
        have e1 : (∑ v, (y v : ℝ) * (p v : ℝ)) = ∑ i, (p i : ℝ) * (y i : ℝ) :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        have e2 : (∑ v, (x v : ℝ) * (p v : ℝ)) = a :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rw [e1, e2] at h2
        linarith
    · apply le_sSup
      refine ⟨x, ?_⟩
      rw [← hr, ib7d_toE_real, ← EReal.coe_sub]
  have hfp : ConvexConjugate f p = ((a - r : ℝ) : WithTop ℝ) := by
    unfold ConvexConjugate; rw [hS1]; rfl
  -- upper bound: every term ≤ r
  have hub : ∀ q : V → ℤ,
      ((∑ i, (x i : ℝ) * (q i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate f q) ≤ ((r : ℝ) : EReal) := by
    intro q
    set T := sSup {v : EReal | ∃ y : V → ℤ,
      v = ((∑ i, (q i : ℝ) * (y i : ℝ) : ℝ) : EReal) - ToEReal (f y)} with hT
    have hTge : ((∑ i, (q i : ℝ) * (x i : ℝ) - r : ℝ) : EReal) ≤ T := by
      apply le_sSup
      refine ⟨x, ?_⟩
      rw [← hr, ib7d_toE_real, ← EReal.coe_sub]
    have hTne : T ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hTge
    have hcc : ConvexConjugate f q = FromEReal T := rfl
    rw [hcc, ib7d_toE_fromE T hTne]
    have e3 : (∑ i, (x i : ℝ) * (q i : ℝ)) = ∑ i, (q i : ℝ) * (x i : ℝ) :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e3]
    clear_value T
    induction T using EReal.rec with
    | bot => exact absurd rfl hTne
    | top => rw [EReal.sub_top]; exact bot_le
    | coe t =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := EReal.coe_le_coe_iff.mp hTge
      linarith
  have hS2 : sSup {v : EReal | ∃ q : V → ℤ,
      v = ((∑ i, (x i : ℝ) * (q i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate f q)} = ((r : ℝ) : EReal) := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨q, rfl⟩
      exact hub q
    · apply le_sSup
      refine ⟨p, ?_⟩
      rw [hfp, ib7d_toE_real, ← EReal.coe_sub]
      congr 1
      have e4 : (∑ i, (x i : ℝ) * (p i : ℝ)) = a :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [e4]; ring
  have hfin : ConvexConjugate (ConvexConjugate f) x = FromEReal (sSup {v : EReal | ∃ q : V → ℤ,
      v = ((∑ i, (x i : ℝ) * (q i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate f q)}) := rfl
  rw [hfin, hS2, ← hr]
  rfl
