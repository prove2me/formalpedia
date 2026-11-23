-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.pt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:14.439664+00:00
-- url     : https://prove2.me/submissions/d366bc9a-7040-454b-b9a6-0b8aaaa55cd4

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_cnd_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_level_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {E : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (p : TB.Pt E) :
    ∀ n, p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p := by
  suffices HH : ∀ n (p : TB.Pt E), p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p from
    fun n => HH n p
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro p
  cases n with
  | zero =>
    rw [TA.PT]
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
    · rintro ⟨hl, hc⟩
      obtain rfl | ⟨h, ⟨s, t⟩, hp⟩ := List.eq_nil_or_concat p
      · rfl
      · exfalso
        try rw [List.concat_eq_append] at hp
        subst hp
        obtain ⟨-, hs, -⟩ := (cnd_append Sg h s t).mp hc
        rw [level_append] at hl
        omega
  | succ n =>
    rw [TA.PT]
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range,
      Finset.mem_image, TA.ext]
    constructor
    · rintro ⟨m, hm, h, hh, t, ht, rfl⟩
      obtain ⟨hl, hc⟩ := (ih m hm h).mp hh
      have e : n + 1 - (n + 1 - m) + 1 = m + 1 := by omega
      rw [e] at ht
      refine ⟨?_, (cnd_append Sg h _ t).mpr ⟨hc, by omega, ?_⟩⟩
      · rw [level_append, hl]
        omega
      · rw [hl]
        exact ht
    · rintro ⟨hl, hc⟩
      obtain rfl | ⟨h, ⟨s, t⟩, hp⟩ := List.eq_nil_or_concat p
      · simp [TB.level] at hl
      · try rw [List.concat_eq_append] at hp
        subst hp
        obtain ⟨hc', hs, ht⟩ := (cnd_append Sg h s t).mp hc
        rw [level_append] at hl
        have hm : TB.level h < n + 1 := by omega
        have e1 : n + 1 - TB.level h = s := by omega
        have e2 : n + 1 - s + 1 = TB.level h + 1 := by omega
        refine ⟨TB.level h, hm, h, (ih _ hm h).mpr ⟨rfl, hc'⟩, t, ?_, ?_⟩
        · rw [e1, e2]
          exact ht
        · rw [e1]
end Formalism.FourierDecayAlt.P.Jx1
