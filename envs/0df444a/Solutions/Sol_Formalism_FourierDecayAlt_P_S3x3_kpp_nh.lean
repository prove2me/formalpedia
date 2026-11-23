-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.kpp_nh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:49.553061+00:00
-- url     : https://prove2.me/submissions/903b365d-785b-43f8-8f46-c039c4dfccc8

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_hEmb
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_of_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_inGLo_nh
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
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsFractionRing o k0]
variable [IsLocalRing o]
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) :
    (∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = n * hEmb r h) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h := by
  have hinj := IsFractionRing.injective o k0
  constructor
  · rintro ⟨y, ⟨hdet, hNU⟩, hy⟩
    obtain ⟨hn', yh, hyh, rfl⟩ := (inGLo_nh o hn hh).1 ⟨y, hdet, hy⟩
    refine ⟨hn', yh, hyh, ?_, rfl⟩
    obtain ⟨yn, hyn, rfl⟩ := hn'
    have e : y = yn * hEmb r yh := by
      apply Matrix.map_injective hinj
      show y.map (algebraMap o k0) = (yn * hEmb r yh).map (algebraMap o k0)
      rw [hy, Matrix.map_mul, hEmb_map]
    subst e
    obtain ⟨n', u', hn', ⟨u, hu, rfl⟩, e⟩ := hNU
    have hN := isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn)
    have e2 := congrArg b22 e
    rw [Matrix.map_mul, hEmb_map, block22_mul_levi_embedding, block22_mul_levi_embedding, hN.2.2.1, hn'.2.2.1, one_mul,
      one_mul] at e2
    rw [midEmb_inj e2]
    exact hu
  · rintro ⟨⟨yn, hyn, rfl⟩, yh, hyh, hu, rfl⟩
    refine ⟨yn * hEmb r yh, ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.det_mul, det_hEmb]; exact hyn.mul hyh
    · rw [Matrix.map_mul, hEmb_map]
      exact ⟨_, _, isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn), ⟨_, hu, rfl⟩, rfl⟩
    · rw [Matrix.map_mul, hEmb_map]
end Formalism.FourierDecayAlt.P.S3x3
