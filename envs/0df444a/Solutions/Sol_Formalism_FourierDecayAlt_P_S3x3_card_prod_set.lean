-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.card_prod_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:51.396581+00:00
-- url     : https://prove2.me/submissions/8614373c-5cc6-483c-a4f5-c6665b3a8679

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_hEmb
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_GL_subtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_mul_levi_embedding

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution (Q : Matrix (Fin k) (Fin k) A → Prop) (hQ : ∀ h, Q h → IsUnit h.det) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) A //
        ∃ n h', IsN n ∧ (∃ h, Q h ∧ h' = hEmb r h) ∧ x = n * h'} =
      Nat.card {g : GL (Fin k) A // Q g} * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  rw [card_GL_subtype Q hQ, ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.2.1 * hEmb r p.1.1, p.2.1, hEmb r p.1.1, p.2.2, ⟨p.1.1, p.1.2, rfl⟩, rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨g, hg⟩, ⟨n, hn⟩⟩ ⟨⟨g', hg'⟩, ⟨n', hn'⟩⟩ e
    have e1 : n * hEmb r g = n' * hEmb r g' := congrArg Subtype.val e
    have e2 := congrArg b22 e1
    rw [block22_mul_levi_embedding, block22_mul_levi_embedding, hn.2.2.1, hn'.2.2.1, one_mul, one_mul] at e2
    have e3 : g = g' := midEmb_inj e2
    subst e3
    have hu : IsUnit (hEmb r g) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_hEmb]; exact hQ g hg)
    have e4 : n = n' := hu.mul_left_injective e1
    subst e4
    rfl
  · rintro ⟨x, n, h', hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨⟨⟨h, hh⟩, ⟨n, hn⟩⟩, rfl⟩
end Formalism.FourierDecayAlt.P.S3x3
