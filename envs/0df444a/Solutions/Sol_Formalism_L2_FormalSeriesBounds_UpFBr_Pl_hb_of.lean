-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.hb_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:25.783161+00:00
-- url     : https://prove2.me/submissions/f517c6c4-1ae3-41ad-af57-a33c4a222940

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution {ι : Type} [Fintype ι] (e : ℤ_[l] ⊗[ℤ] OE)
    (b : Module.Basis ι ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) (x : ℤ_[l] ⊗[ℤ] OE) :
    ∃ r : ι → ℤ_[l], e * x = ∑ i, r i • (b i : ℤ_[l] ⊗[ℤ] OE) := by
  have hy : e * x ∈ LinearMap.range (LinearMap.mulLeft ℤ_[l] e) := ⟨x, by simp⟩
  refine ⟨b.repr ⟨e * x, hy⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_repr ⟨e * x, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h.symm
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
