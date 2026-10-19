-- Prove2me | solution 1 for ContWeatherall.essSurj_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:35:29.234994+00:00
-- url     : https://prove2.me/submissions/9c77f37b-0866-4e1b-bca4-5af2f045a2fa

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff
open ContWeatherall
/-- `A ↦ dA` is essentially surjective iff `H² = 0` on the `P`-sector. -/


theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) :
    (fieldStrength P).EssSurj ↔ H2Vanishes P := by
  constructor
  · intro hes B hB hdB hPB
    obtain ⟨A, ⟨i⟩⟩ := hes.mem_essImage (Discrete.mk ⟨B, hB, hdB, hPB⟩)
    have h := Discrete.eq_of_hom i.hom
    refine ⟨A.pot, A.smooth, ?_⟩
    exact congrArg Subtype.val h
  · intro hH
    refine ⟨fun Y => ?_⟩
    obtain ⟨⟨B, hB, hdB, hPB⟩⟩ := Y
    obtain ⟨A, hA, hdA⟩ := hH B hB hdB hPB
    refine ⟨⟨A, hA, by rw [hdA]; exact hPB⟩, ⟨eqToIso ?_⟩⟩
    show Discrete.mk _ = Discrete.mk _
    congr 1
    exact Subtype.ext hdA


