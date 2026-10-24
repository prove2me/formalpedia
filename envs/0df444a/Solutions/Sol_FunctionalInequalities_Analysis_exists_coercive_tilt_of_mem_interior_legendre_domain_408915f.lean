-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:15:23.525705+00:00
-- url     : https://prove2.me/submissions/e3fe529d-00b6-4e0c-811e-f4c9aa72d700

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
import Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_408915f

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

section
noncomputable section
open Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A simplex in the original open neighborhood supplies a finite witness whose
convex hull still contains a neighborhood of zero, including dimension zero. -/
theorem FunctionalInequalities.Analysis.exists_finite_hull_neighborhood [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsOpen K) (h0 : (0 : E) ∈ K) :
    ∃ (s : Finset E) (_hs : s.Nonempty), (↑s : Set E) ⊆ K ∧
      (0 : E) ∈ interior (convexHull ℝ (↑s : Set E)) := by
  classical
  obtain ⟨b, hb0, hbK⟩ := exists_mem_interior_convexHull_affineBasis (hK.mem_nhds h0)
  let s : Finset E := Finset.univ.image b
  have heq : (↑s : Set E) = range b := by simp [s]
  refine ⟨s, Finset.univ_nonempty.image b, ?_, ?_⟩
  · rw [heq]
    exact (subset_convexHull ℝ (range b)).trans hbK
  · rwa [heq]
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
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A finite dual neighborhood forces linear growth of the actual tilted
primal, without convexity, differentiability, nonnegativity or global
finiteness of the primal. Dimension zero is included. -/
theorem solution
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}) :
    ∃ (a b : ℝ), 0 < a ∧ ∀ z : E,
      ((a * ‖z‖ - b : ℝ) : EReal) ≤ φ z - (inner ℝ z y : EReal) := by
    let K : Set E := (fun w : E => y + w) ⁻¹' interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}
    have hK : IsOpen K := by
      dsimp [K]
      exact isOpen_interior.preimage (continuous_const.add continuous_id)
    have h0K : 0 ∈ K := by
      dsimp [K]
      simpa using hy
    obtain ⟨s, hs, hsK, h0⟩ := FunctionalInequalities.Analysis.exists_finite_hull_neighborhood hK h0K
    let d : E → ℝ := fun w => (FunctionalInequalities.Analysis.legendre φ (y + w)).toReal
    let M : ℝ := s.sup' hs d
    have hbound : ∀ w ∈ s, d w ≤ M := by
      intro w hw
      exact Finset.le_sup' d hw
    obtain ⟨c, hc, hcoercive⟩ :=
      FunctionalInequalities.Analysis.affineMaximum_coercive_408915f s hs h0
    refine ⟨c, M, hc, ?_⟩
    intro z
    have hlower :
        ((c * ‖z‖ - M : ℝ) : EReal) ≤
          (FunctionalInequalities.Analysis.affineMaximum s hs d z : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (hcoercive d M hbound z)
    obtain ⟨w, hw, hw_eq⟩ :=
      Finset.exists_mem_eq_sup' hs (fun w => inner ℝ w z - d w)
    have hwD : y + w ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤} := hsK hw
    have htop : FunctionalInequalities.Analysis.legendre φ (y + w) ≠ ⊤ := interior_subset hwD
    have hbot : FunctionalInequalities.Analysis.legendre φ (y + w) ≠ ⊥ :=
      FunctionalInequalities.Analysis.legendre_ne_bot φ hφ (y + w)
    have hleg : FunctionalInequalities.Analysis.legendre φ (y + w) = (d w : EReal) := by
      dsimp [d]
      symm
      exact EReal.coe_toReal htop hbot
    have hfen := FunctionalInequalities.Analysis.fenchel_le φ hφ z (y + w)
    rw [hleg] at hfen
    have hsub :
        ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) ≤ φ z := by
      calc
        ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) ≤
            (φ z + (d w : EReal)) - (d w : EReal) :=
          EReal.sub_le_sub hfen (le_refl _)
        _ = φ z := EReal.add_sub_cancel_right
    have hvertex :
        ((inner ℝ w z - d w : ℝ) : EReal) ≤
          φ z - (inner ℝ z y : EReal) := by
      apply
        (EReal.le_sub_iff_add_le
          (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).2
      calc
        ((inner ℝ w z - d w : ℝ) : EReal) + (inner ℝ z y : EReal) =
            ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) := by
              rw [EReal.coe_sub, inner_add_right, EReal.coe_add,
                real_inner_comm w z]
              simp only [sub_eq_add_neg]
              ac_rfl
        _ ≤ φ z := hsub
    have hupper :
        (FunctionalInequalities.Analysis.affineMaximum s hs d z : EReal) ≤
          φ z - (inner ℝ z y : EReal) := by
      rw [FunctionalInequalities.Analysis.affineMaximum, hw_eq]
      exact hvertex
    exact hlower.trans hupper
