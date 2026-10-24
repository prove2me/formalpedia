-- Prove2me | solution 1 for FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:42.208831+00:00
-- url     : https://prove2.me/submissions/90ab9b7e-3440-4d8f-bafc-1816a2a0d376

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
/-- Fenchel inequality for a proper extended potential; no convexity is assumed. -/
theorem FunctionalInequalities.Analysis.fenchel_le (φ : E → EReal) (hφ : ProperPotential φ) (x y : E) :
    (inner ℝ x y : EReal) ≤ φ x + legendre φ y := by
  have h := le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x
  have hi := (EReal.sub_le_iff_le_add (.inl (hφ.1 x))
    (.inr (legendre_ne_bot φ hφ y))).mp h
  simpa only [add_comm] using hi
end
end
end
end

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section MaximizerGradient
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Identification part of the dual-differentiability argument in
Berman--Berndtsson arXiv:1207.6128v1 Lemma 2.7 / Appendix 6, needed for
CEK arXiv:1304.0630v1 first variation. Every actual maximizing affine term
equals the actual dual gradient. The primal need not be differentiable,
convex, nonnegative or finite everywhere. Existence of a maximizing point
and the envelope derivative remain separate results. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    {y : E} (hy : y ∈ interior {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ
      (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
    ∀ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y →
      z = gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y := by
    intro z hz
    let F : E → ℝ :=
      fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal
    let S : Set E :=
      {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}

    have hyS : y ∈ interior S := by
      simpa [S] using hy
    have hy_mem : y ∈ S := interior_subset hyS
    have hy_top :
        FunctionalInequalities.Analysis.legendre φ y ≠ ⊤ := by
      simpa [S] using hy_mem
    have hy_bot :
        FunctionalInequalities.Analysis.legendre φ y ≠ ⊥ :=
      FunctionalInequalities.Analysis.legendre_ne_bot φ hφ y

    have hz_top : φ z ≠ ⊤ := by
      intro hztop
      have hbot : (inner ℝ z y : EReal) - φ z = ⊥ := by
        rw [hztop, EReal.sub_top]
      rw [hbot] at hz
      exact hy_bot hz.symm

    have hz_bot : φ z ≠ ⊥ := hφ.1 z
    have hzcoe : (↑((φ z).toReal) : EReal) = φ z :=
      EReal.coe_toReal hz_top hz_bot
    have hycoe :
        (↑((FunctionalInequalities.Analysis.legendre φ y).toReal) : EReal) =
          FunctionalInequalities.Analysis.legendre φ y :=
      EReal.coe_toReal hy_top hy_bot

    have heqE :
        (↑(inner ℝ z y - (φ z).toReal) : EReal) =
          FunctionalInequalities.Analysis.legendre φ y := by
      calc
        (↑(inner ℝ z y - (φ z).toReal) : EReal) =
            (inner ℝ z y : EReal) - (↑((φ z).toReal) : EReal) :=
          EReal.coe_sub _ _
        _ = (inner ℝ z y : EReal) - φ z := by rw [hzcoe]
        _ = FunctionalInequalities.Analysis.legendre φ y := hz

    have hyreal :
        inner ℝ z y - (φ z).toReal =
          (FunctionalInequalities.Analysis.legendre φ y).toReal := by
      have h := congrArg EReal.toReal heqE
      simpa only [EReal.toReal_coe] using h

    have hS : S ∈ nhds y := by
      exact Filter.mem_of_superset (isOpen_interior.mem_nhds hyS) interior_subset

    have hineq (q : E) (hq : q ∈ S) :
        inner ℝ z q - (φ z).toReal ≤
          (FunctionalInequalities.Analysis.legendre φ q).toReal := by
      have hq_top :
          FunctionalInequalities.Analysis.legendre φ q ≠ ⊤ := by
        simpa [S] using hq
      have hq_bot :
          FunctionalInequalities.Analysis.legendre φ q ≠ ⊥ :=
        FunctionalInequalities.Analysis.legendre_ne_bot φ hφ q
      have hqcoe :
          (↑((FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) =
            FunctionalInequalities.Analysis.legendre φ q :=
        EReal.coe_toReal hq_top hq_bot
      have hfen :=
        FunctionalInequalities.Analysis.fenchel_le φ hφ z q
      have hfen' :
          (inner ℝ z q : EReal) ≤
            (↑((φ z).toReal) : EReal) +
              (↑((FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) := by
        simpa [hzcoe, hqcoe] using hfen
      have hfen'' :
          (inner ℝ z q : EReal) ≤
            (↑((φ z).toReal +
                (FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) := by
        simpa using hfen'
      have hreal :
          inner ℝ z q ≤
            (φ z).toReal +
              (FunctionalInequalities.Analysis.legendre φ q).toReal :=
        EReal.coe_le_coe_iff.mp hfen''
      linarith

    have hlocal : IsLocalMax (fun q : E => inner ℝ z q - F q) y := by
      change ∀ᶠ q in nhds y,
        inner ℝ z q - F q ≤ inner ℝ z y - F y
      filter_upwards [hS] with q hq
      dsimp [F]
      linarith [hineq q hq, hyreal]

    have hzero :
        fderiv ℝ (fun q : E => inner ℝ z q - F q) y = 0 :=
      hlocal.fderiv_eq_zero

    have hinner :
        HasFDerivAt (fun q : E => inner ℝ z q)
          (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) y := by
      simpa [id] using
        ((hasFDerivAt_const (𝕜 := ℝ) z y).inner ℝ
          (hasFDerivAt_id (𝕜 := ℝ) y))

    have hF : DifferentiableAt ℝ F y := by
      simpa [F] using hd

    have hsub := hinner.sub hF.hasFDerivAt
    have hsubf := hsub.fderiv

    have hder :
        (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) -
          fderiv ℝ F y = 0 := by
      calc
        (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) -
            fderiv ℝ F y =
            fderiv ℝ (fun q : E => inner ℝ z q - F q) y := by
              symm
              simpa only [Pi.sub_def] using hsubf
        _ = 0 := hzero

    have hrel (v : E) : inner ℝ z v = fderiv ℝ F y v := by
      have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) hder
      have hv' : inner ℝ z v - fderiv ℝ F y v = 0 := by
        simpa [fderivInnerCLM] using hv
      linarith

    have hrel' (v : E) :
        inner ℝ z v = inner ℝ (gradient F y) v := by
      calc
        inner ℝ z v = fderiv ℝ F y v := hrel v
        _ = inner ℝ (gradient F y) v :=
          (inner_gradient_left (f := F) (x := y) (y := v)).symm

    have hz0 : z - gradient F y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      calc
        inner ℝ (z - gradient F y) (z - gradient F y) =
            inner ℝ z (z - gradient F y) -
              inner ℝ (gradient F y) (z - gradient F y) := by
                rw [inner_sub_left]
        _ = 0 := by rw [hrel' (z - gradient F y)]; ring

    change z = gradient F y
    exact sub_eq_zero.mp hz0
