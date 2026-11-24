-- Prove2me | solution 1 for Formalism.L2.Pj.RegB.mem_loc_of_heightOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:48.606409+00:00
-- url     : https://prove2.me/submissions/885662b6-cc1d-4f16-a63b-73ae982ac0b6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_KrullColonIdeal_mem_colonI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegB
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal
namespace Formalism.L2.Pj.RegB
theorem _root_.solution {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (qq : Ideal R) [hq : qq.IsPrime]
    (x : K) (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p ≤ qq →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ a s : R, s ∉ qq ∧ x * algebraMap R K s = algebraMap R K a := by
  classical
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors R) x
  simp only at hxs
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsK : algebraMap R K (s : R) ≠ 0 := by
    intro h; apply hs0; exact hinj (by rw [h, map_zero])
  by_cases hex : ∃ t : R, t ∉ qq ∧ t * a ∈ Ideal.span {(s : R)}
  · obtain ⟨t, ht, hta⟩ := hex
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hta
    refine ⟨r, t, ht, ?_⟩
    apply mul_right_cancel₀ hsK
    rw [mul_assoc, mul_comm (algebraMap R K t), ← mul_assoc, hxs, ← map_mul, ← map_mul, mul_comm a t, ← hr,
      mul_comm]
  push Not at hex
  have hab0 : colonI (s : R) a ≤ qq := by
    intro t ht
    by_contra htq
    exact hex t htq ht
  let S : Set (Ideal R) := {J | ∃ c, J = colonI (s : R) c ∧ J ≤ qq ∧ colonI (s : R) a ≤ J}
  have hS : S.Nonempty := ⟨colonI (s : R) a, a, rfl, hab0, le_rfl⟩
  obtain ⟨J, ⟨b, rfl, hJq, hab⟩, hmax⟩ := (wellFounded_gt (α := Ideal R)).has_min S hS

  have hsat : ∀ r : R, r ∉ qq → colonI (s : R) (r * b) = colonI (s : R) b := by
    intro r hr
    have hle : colonI (s : R) b ≤ colonI (s : R) (r * b) := by
      intro y hy
      rw [mem_colonI] at *
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
    have hq' : colonI (s : R) (r * b) ≤ qq := by
      intro y hy
      rw [mem_colonI, ← mul_assoc] at hy
      have : y * r ∈ qq := hJq hy
      rcases hq.mem_or_mem this with h | h
      · exact h
      · exact absurd h hr
    by_contra hne
    exact hmax _ ⟨r * b, rfl, hq', hab.trans hle⟩ (lt_of_le_of_ne hle (Ne.symm hne))
  set P := colonI (s : R) b with hPdef
  have hPne : P ≠ ⊤ := fun h => hq.ne_top (top_le_iff.1 (h ▸ hJq))
  have hb : b ∉ Ideal.span {(s : R)} := by
    intro hb
    apply hPne
    rw [eq_top_iff]
    intro y _
    rw [mem_colonI]
    exact Ideal.mul_mem_left _ _ hb
  have hprime : ∀ q1 q2 : R, q1 * q2 ∈ P → q1 ∈ P ∨ q2 ∈ P := by
    intro q1 q2 hq12
    by_cases h1 : q1 ∈ P
    · exact Or.inl h1
    · right
      have hle : P ≤ colonI (s : R) (q1 * b) := by
        intro y hy
        rw [mem_colonI] at *
        rw [mul_left_comm]
        exact Ideal.mul_mem_left _ _ hy
      have hq' : colonI (s : R) (q1 * b) ≤ qq := by
        intro y hy
        by_contra hyq
        apply h1
        rw [← hsat y hyq, mem_colonI]
        rw [mem_colonI] at hy
        have : q1 * (y * b) = y * (q1 * b) := by ring
        rw [this]
        exact hy
      have heq : P = colonI (s : R) (q1 * b) := by
        by_contra hne
        exact hmax _ ⟨q1 * b, rfl, hq', hab.trans hle⟩ (lt_of_le_of_ne hle hne)
      rw [heq, mem_colonI]
      rw [mem_colonI] at hq12
      have : q2 * (q1 * b) = q1 * q2 * b := by ring
      rw [this]
      exact hq12
  have hPp : P.IsPrime := ⟨hPne, fun {q1 q2} h => hprime q1 q2 h⟩
  have hsP : (s : R) ∈ P := by
    rw [mem_colonI]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hPbot : P ≠ ⊥ := by
    intro h
    apply hs0
    rw [h] at hsP
    exact (Submodule.mem_bot R).mp hsP

  have hle1 : P.height ≤ 1 := by
    by_cases hA : ∀ q ∈ P, ∀ t : R, q * b = t * s → t ∈ P
    · exfalso
      let y : K := algebraMap R K b / algebraMap R K s
      let N : Submodule R K := Submodule.map (Algebra.linearMap R K) P
      have hN : N ≠ ⊥ := by
        intro h
        have : algebraMap R K (s : R) ∈ N := ⟨s, hsP, rfl⟩
        rw [h] at this
        exact hsK ((Submodule.mem_bot R).mp this)
      have hNfg : N.FG := (IsNoetherian.noetherian P).map _
      have hint : IsIntegral R y := by
        refine isIntegral_of_smul_mem_submodule N hN hNfg y ?_
        rintro n ⟨q, hq, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ((mem_colonI).mp hq)
        refine ⟨t, hA q hq t ht.symm, ?_⟩
        simp only [Algebra.linearMap_apply, smul_eq_mul, y]
        field_simp
        rw [← map_mul, ← map_mul, ht, mul_comm]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      apply hb
      rw [Ideal.mem_span_singleton']
      refine ⟨r, hinj ?_⟩
      rw [map_mul, hr]
      simp only [y]
      field_simp
    · push Not at hA
      obtain ⟨u, hu, t, hut, htP⟩ := hA
      have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
      apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {u}) P
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).mpr hu⟩, ?_⟩
      rintro Q ⟨hQ, huQ⟩ hQP q hq
      obtain ⟨tq, htq⟩ := Ideal.mem_span_singleton'.mp ((mem_colonI).mp hq)
      have key : q * t = u * tq := by
        apply mul_right_cancel₀ hs0
        calc q * t * s = q * (u * b) := by rw [hut]; ring
          _ = u * (q * b) := by ring
          _ = u * tq * s := by rw [← htq]; ring
      have hu' : u ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp huQ
      have : q * t ∈ Q := by rw [key]; exact Ideal.mul_mem_right _ _ hu'
      rcases hQ.mem_or_mem this with h | h
      · exact h
      · exact absurd (hQP h) htP
  have hne0 : P.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hPbot
  have h1 : P.height = 1 := le_antisymm hle1 (Order.one_le_iff_ne_zero.mpr hne0)
  obtain ⟨a', s', hs'P, hxs'⟩ := hx P hPp h1 hJq
  exfalso
  apply hs'P
  apply hab
  rw [mem_colonI, Ideal.mem_span_singleton']
  refine ⟨a', hinj ?_⟩
  rw [map_mul, map_mul, ← hxs', ← hxs]
  ring
end Formalism.L2.Pj.RegB
