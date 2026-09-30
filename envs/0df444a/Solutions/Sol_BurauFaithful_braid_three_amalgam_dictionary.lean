-- Prove2me | solution 1 for BurauFaithful.braid_three_amalgam_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T06:57:39.607988+00:00
-- url     : https://prove2.me/submissions/192156f3-450e-4bd9-9a03-fff228f0fd69

/-
`BurauFaithful.braid_three_amalgam_dictionary` — proof file.

NOTE (platform): the *target's* preamble already declares `BurauFaithful.sLift` and
`BurauFaithful.uLift`, so this file must use **differently named** local copies (SESSION 6 rule);
the type of `solution` is then only definitionally equal to the target's, which the checker accepts.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

namespace BurauFaithful

/-- Local copy (renamed to avoid the target's preamble): `σ₀²σ₁`. -/
noncomputable def sLiftAux : PresentedGroup (BraidsLinksMCG.braidRels 3) :=
  PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) ^ 2 *
    PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1

/-- Local copy (renamed to avoid the target's preamble): `σ₀σ₁`. -/
noncomputable def uLiftAux : PresentedGroup (BraidsLinksMCG.braidRels 3) :=
  PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
    PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1

end BurauFaithful

theorem solution :
    ((PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) =
        BurauFaithful.sLiftAux * BurauFaithful.uLiftAux⁻¹) ∧
      (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (1 : Fin 2) =
        BurauFaithful.uLiftAux * BurauFaithful.sLiftAux⁻¹ * BurauFaithful.uLiftAux) ∧
      (BurauFaithful.sLiftAux ^ 2 = BurauFaithful.uLiftAux ^ 3) ∧
      (BurauFaithful.sLiftAux =
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
          BurauFaithful.uLiftAux)) := by
  have hrel : PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 =
      PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 := by
    have hmem : (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
        (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) ∈
        Subgroup.normalClosure (BraidsLinksMCG.braidRels 3) :=
      Subgroup.subset_normalClosure (by
        rw [BraidsLinksMCG.braidRels]
        exact Or.inr ⟨0, 1, by decide, rfl⟩)
    have h1 : PresentedGroup.mk (BraidsLinksMCG.braidRels 3)
        (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
          (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr hmem
    have h2 : PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
        PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
        (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
          PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
          PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1)⁻¹ = 1 := by
      rw [← h1]
      simp only [PresentedGroup.of, map_mul, map_inv]
    exact mul_inv_eq_one.mp h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [BurauFaithful.sLiftAux, BurauFaithful.uLiftAux]
    group
  · simp only [BurauFaithful.sLiftAux, BurauFaithful.uLiftAux]
    group
  · calc BurauFaithful.sLiftAux ^ 2
        = PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
            (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0) *
            (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1) := by
          simp only [BurauFaithful.sLiftAux, pow_two, mul_assoc]
      _ = PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) (0 : Fin 2) *
            (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1) *
            (PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 0 *
              PresentedGroup.of (rels := BraidsLinksMCG.braidRels 3) 1) := by rw [hrel]
      _ = BurauFaithful.uLiftAux ^ 3 := by
          simp only [BurauFaithful.uLiftAux, pow_succ, pow_two, pow_zero, one_mul, mul_assoc]
  · simp only [BurauFaithful.sLiftAux, BurauFaithful.uLiftAux, pow_two, mul_assoc]
