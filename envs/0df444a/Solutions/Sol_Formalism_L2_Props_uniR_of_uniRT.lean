-- Prove2me | solution 1 for Formalism.L2.Props.uniR_of_uniRT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:01.798027+00:00
-- url     : https://prove2.me/submissions/34e7304e-fdb8-4da5-80cc-c5dff4fda964

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLevel
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Props
open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}
namespace Formalism.L2.Props
theorem _root_.solution {s : SplitPlace L} {r : ℕ} {h : GL (Fin n) (s.v.adicCompletion L⁺)} (hh : UniRT s r h) :
    UniR r h := by
  unfold UniR
  refine ⟨?_, hh.2⟩
  unfold ParaR
  obtain ⟨⟨g, hg⟩, hlow⟩ := hh.1
  refine ⟨?_, ?_, hlow⟩
  · intro a b
    rw [← hg]
    exact (g.val a b).2
  · intro a b
    rw [← hg, ← map_inv]
    exact (g⁻¹.val a b).2
end Formalism.L2.Props
