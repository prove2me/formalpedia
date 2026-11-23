-- Prove2me | solution 1 for Formalism.L2.DIV.IsBaseChar.good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:31.830689+00:00
-- url     : https://prove2.me/submissions/27f3f9d4-9a0e-4256-93f5-83374ca6b7e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_tupGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
namespace IsBaseChar
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type}
    [Field L] {S : Set ℕ} {p : ℕ} (δ : Tup F E L S) (h : IsBaseChar p (δ : Chr F E L))
    (v : HeightOneSpectrum (𝓞 F)) (hv : plc v = p) : GoodPl E S v := by
  by_contra hg
  have h1 : (δ : Chr F E L) ∈ kills Lˣ (inertAt E v) := by
    exact ((mem_tupGrp (δ : Chr F E L)).mp δ.2).2.2.2 v hg
  have h2 : (15 : ℕ) ∣ 1 := ((h.2 v).1 hv 1).mp fun x hx => by
    have := h1 hx
    rw [MonoidHom.mem_ker] at this
    rw [this, one_pow]
  omega
end IsBaseChar
end Formalism.L2.DIV
