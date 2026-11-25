-- Prove2me | solution 1 for CompanionTheory.L3H.tSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:24.893911+00:00
-- url     : https://prove2.me/submissions/568cf25e-ede0-49e6-99d2-0d5dfb850812

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Theorems.Thm_CompanionTheory_Split_emb_loc
import Theorems.Thm_CompanionTheory_Split_emb_triv
import Theorems.Thm_CompanionTheory_Split_loc_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L) (n)
variable {n}
namespace CompanionTheory.L3H
theorem _root_.solution {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) (x : Formalism.AUTREP.GAf L n) :
    x ∈ Formalism.AUTREP.tSet L n s ϖ k ↔ ∃ h ∈ DoubleCoset.doubleCoset (dg n s h0 k) (KL s n : Set _) (KL s n), emb s n h = x := by
  constructor
  · rintro ⟨hx, a, ha, b, hb, e⟩
    refine ⟨s.loc n x, DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, Units.ext ?_⟩, emb_loc s hx⟩
    rw [Units.val_mul, Units.val_mul]
    exact e
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    exact ⟨emb_triv s _, a, ha, b, hb, by rw [loc_emb]; rfl⟩
end CompanionTheory.L3H
