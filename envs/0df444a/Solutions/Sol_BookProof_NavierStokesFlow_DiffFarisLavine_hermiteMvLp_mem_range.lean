-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.hermiteMvLp_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:17:49.839427+00:00
-- url     : https://prove2.me/submissions/cf913616-ef48-4e11-89d4-c5ddcd2ed31b

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

private theorem embedCore_coe (x : lpFiniteModes Vel) :
    ((embedCore x : polyGaussCore (d := 3)) : L2d 3) = velUnitary ((x : L2I Vel)) := rfl

private theorem coreEquiv_coe (p : MvPolynomial (Fin 3) ℂ) :
    ((coreEquiv p : polyGaussCore (d := 3)) : L2d 3) = pgLp p := rfl
private theorem pgLp_smul (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) : pgLp (c • p) = c • pgLp p :=
  map_smul (pgMap (d := 3)) c p
private theorem embedCore_coreState (b : Vel) :
    embedCore (coreState b)
      = coreEquiv (((hermiteMvNorm (velIdx b) : ℝ) : ℂ)⁻¹ • hermiteMv (velIdx b)) := by
  refine Subtype.ext ?_
  rw [coreEquiv_coe, embedCore_coe, coreState_coe, velUnitary_single, hermiteVel, hermiteMvLp,
    pgLp_smul]

theorem solution (a : Fin 3 →₀ ℕ) :
    hermiteMvLp a
      ∈ Submodule.map ((polyGaussCore (d := 3)).subtype) (LinearMap.range embedCore) := by
  refine ⟨embedCore (coreState (velIdx.symm a)), ⟨_, rfl⟩, ?_⟩
  rw [embedCore_coreState, Submodule.subtype_apply, coreEquiv_coe, pgLp_smul,
    Equiv.apply_symm_apply]
  rfl

#print axioms solution
