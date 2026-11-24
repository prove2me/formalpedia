-- Prove2me | solution 1 for Formalism.L2.PjFree.intAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:43.238248+00:00
-- url     : https://prove2.me/submissions/c3a99560-9282-4c5e-8300-7e2bed393b2b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_mem_range_of_vV_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Dvr
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
end Dvr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Open
variable (Xo : Moduli Dw l) (c : Coeff l)
end Open
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
private lemma vV_alg_nonneg_lemma {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  unfold vV valV
  by_cases ha : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) (algebraMap V K' a) = 0
  · simp [ha]
  · have h1 : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) (algebraMap V K' a) ≤ 1 := by
      first
        | exact HeightOneSpectrum.valuation_le_one _ a
        | exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
        | exact HeightOneSpectrum.valuation_le_one (K := K') _ a
        | exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K') a
    rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    linarith
end Proofs
section Frames
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
end Frames
end Formalism.L2.PjFree
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.PjFree
theorem _root_.solution (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hR : ReFrame Xo c) : IntAll Xo c := by
  intro la T io e hO hFin y
  letI := io.toAlgebra
  obtain ⟨T', i, r, hr, hv, hF', y0, hy0⟩ := hE T io hFin y.x y.x_over
  letI := (i.comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hB T.Fr T'.Fr φ y
  obtain ⟨t, y', hy'⟩ := hR T' (i.comp io) y0 z (hz.1.trans hy0.symm)
  refine ⟨T', i.comp io, r * e, y', ?_, hF', φ, z, t, ?_, hz, hy'⟩
  · unfold OverLa at hO ⊢
    refine ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩
    rw [RingHom.comp_apply, hv, hO.2 a]
    push_cast
    ring
  · intro a
    apply mem_range_of_vV_nonneg
    show 0 ≤ vV T'.V (i (algebraMap T.V T.Fr a))
    rw [hv]
    exact mul_nonneg (Nat.cast_nonneg r) (vV_alg_nonneg_lemma a)
end Formalism.L2.PjFree
