-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:38.839217+00:00
-- url     : https://prove2.me/submissions/294d4926-da66-4e28-a4c7-39295e45b6bb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulQ_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {R : Subring K} {s : ℕ} {Cut : Set K} {τ : Kˣ} {F : Kˣ → ℂ}
    {cr : K ⧸ R.toAddSubgroup → Kˣ} (hcr : IsCr R cr)
    (hA : ∀ c c' : Kˣ, (c' : K) - c ∈ R → TT s Cut τ F c' = TT s Cut τ F c)
    (EE : Finset K) (hcard : EE.card ≠ 0) (G : K → Kˣ → ℂ)
    (hB : ∀ ε ∈ EE, ∃ lam : Kˣ, (lam : K) ∈ R ∧ ((lam⁻¹ : Kˣ) : K) ∈ R ∧
      ∀ c, TT s Cut τ F (lam * c) = TT s Cut τ (G ε) c)
    (hC : ∀ c : Kˣ, (c : K) ∈ Cut → ∀ z : Kˣ, z ^ s = τ * c → ∑ ε ∈ EE, G ε z = 0)
    (hfin1 : {x | (cr x : K) ∈ Cut}.Finite) (hfin2 : ∀ D : Kˣ, {z : Kˣ | z ^ s = D}.Finite) :
    ∑ᶠ x, TT s Cut τ F (cr x) = 0 := by
  classical
  have key : ∀ ε ∈ EE, ∑ᶠ x, TT s Cut τ F (cr x) = ∑ᶠ x, TT s Cut τ (G ε) (cr x) := by
    intro ε hε
    obtain ⟨lam, h1, h2, h3⟩ := hB ε hε
    rw [← finsum_comp_equiv (mulQ R lam h1 h2)]
    refine finsum_congr fun x => ?_
    rw [← h3]
    apply hA
    have e1 : ((cr (mulQ R lam h1 h2 x) : K) : K ⧸ R.toAddSubgroup) =
        ((((lam * cr x : Kˣ) : K)) : K ⧸ R.toAddSubgroup) := by
      rw [hcr, Units.val_mul, ← mulQ_mk R lam h1 h2, hcr]
    have e2 := (QuotientAddGroup.eq.1 e1.symm)
    have e3 : -((lam * cr x : Kˣ) : K) + (cr (mulQ R lam h1 h2 x) : K) ∈ R := e2
    convert e3 using 1; ring
  have hsum : (EE.card : ℂ) * ∑ᶠ x, TT s Cut τ F (cr x) = 0 := by
    have h1 : (EE.card : ℂ) * ∑ᶠ x, TT s Cut τ F (cr x) =
        ∑ ε ∈ EE, ∑ᶠ x, TT s Cut τ (G ε) (cr x) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl key
    rw [h1, ← finsum_sum_comm]
    · rw [← finsum_zero (α := K ⧸ R.toAddSubgroup)]
      refine finsum_congr fun x => ?_
      unfold TT
      by_cases hc : (cr x : K) ∈ Cut
      · simp only [if_pos hc]
        rw [← finsum_sum_comm]
        · rw [← finsum_zero (α := Kˣ)]
          refine finsum_congr fun z => ?_
          by_cases hz : z ^ s = τ * cr x
          · simp only [if_pos hz]; exact hC _ hc z hz
          · simp only [if_neg hz]; simp
        · intro ε _
          refine (hfin2 (τ * cr x)).subset ?_
          intro z hz
          by_contra hne
          exact hz (if_neg hne)
      · simp only [if_neg hc]; simp
    · intro ε _
      refine hfin1.subset ?_
      intro x hx
      by_contra hne
      exact hx (if_neg hne)
  rcases mul_eq_zero.1 hsum with h0 | h0
  · exact absurd (by exact_mod_cast h0) hcard
  · exact h0
end Formalism.FourierDecayAlt.P.HenselRootsBounded
