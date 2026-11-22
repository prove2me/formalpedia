-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isoFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:56.995744+00:00
-- url     : https://prove2.me/submissions/e580540e-a386-4f8c-8eb8-6af0fe17dc43

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : IsoFinite := by
  intro K _ R hfin n Z hZ hdet
  obtain ⟨Zr, rfl⟩ : ∃ Zr : Matrix (Fin n) (Fin n) R, Zr.map R.subtype = Z :=
    ⟨liftR R Z hZ, liftR_map R Z hZ⟩
  have hd : ((Zr.det : R) : K) = (Zr.map R.subtype).det := RingHom.map_det R.subtype Zr
  haveI : Finite (R ⧸ Ideal.span {Zr.det}) := hfin Zr.det (by rw [hd]; exact hdet)
  have hmem : ∀ x : Fin n → R, Zr.det • x ∈ latZ R (Zr.map R.subtype) := by
    intro x
    refine (mem_latZ R _ _).2 ⟨Zr.adjugate *ᵥ x, ?_⟩
    rw [coeLin_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_adjugate,
      ← coeLin_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hs := Ideal.Quotient.mk_surjective (I := Ideal.span {Zr.det})
  have hcok : Finite (coker R (Zr.map R.subtype)) := by
    let g : (Fin n → R ⧸ Ideal.span {Zr.det}) → coker R (Zr.map R.subtype) :=
      fun w => Submodule.Quotient.mk (fun j => Function.surjInv hs (w j))
    have hg : Function.Surjective g := by
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨fun j => Ideal.Quotient.mk _ (x j), ?_⟩
      have hc : ∀ j, ∃ c : R,
          Function.surjInv hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j)) - x j
            = Zr.det * c := by
        intro j
        have h1 := Function.surjInv_eq hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j))
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
        exact h1
      choose c hc using hc
      show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
      rw [Submodule.Quotient.eq]
      have hsub : (fun j => Function.surjInv hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j)))
          - x = Zr.det • c := by
        funext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact hc j
      rw [hsub]
      exact hmem c
    exact Finite.of_surjective g hg
  refine ⟨hcok, fun C _ _ e lam => ?_⟩
  by_cases hne : (isoSet R (Zr.map R.subtype) C e lam).Nonempty
  · obtain ⟨φ₀, -⟩ := hne
    haveI := hcok
    haveI : Finite C := Finite.of_surjective φ₀ φ₀.surjective
    haveI : Finite (coker R (Zr.map R.subtype) ≃ₗ[R] C) :=
      Finite.of_injective (fun φ : coker R (Zr.map R.subtype) ≃ₗ[R] C =>
        (φ : coker R (Zr.map R.subtype) → C)) (fun φ ψ h => LinearEquiv.ext (congrFun h))
    exact Set.toFinite _
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty
end Formalism.DoubleCosetMeasures.P
