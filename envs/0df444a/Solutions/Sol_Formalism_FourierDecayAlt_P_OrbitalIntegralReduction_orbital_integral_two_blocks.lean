-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.orbital_integral_two_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.849013+00:00
-- url     : https://prove2.me/submissions/5b5e4808-cfb3-4b8a-a239-bacba8156c54

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_orbZ_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_phase_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_blk_Hm
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_fin_cos
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_low_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_orbZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_phase
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_toCos_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (m : ℕ) (t c : Kˣ)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (π : Kˣ)
    (h1 : ∀ Z a b : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsLowUni a → IsInt R a → IsUpUni b →
      IsInt R b → Φ (m + 1) (a * Z * b) = Φ (m + 1) Z)
    (h2 : ∀ Z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, Φ (m + 1) Z ≠ 0 → IsInt R ((π : K) • Z)) :
    omPhi R ψ (pt2 h0 m t c) Φ =
      ∑ᶠ q : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1)), ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q))) := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => psi_R hD hr
  let w : Point K := addBlock (addBlock h0 m t) 1 c
  let F : lowW K w.1 w.2 × upUniG K w.1.sum → ℂ := fun p => Φ w.1.sum (orbZ w p) * phase ψ p
  have hFinv : ∀ a ∈ intSub R (lowW K w.1 w.2), ∀ b ∈ intSub R (upUniG K w.1.sum),
      ∀ (x : lowW K w.1 w.2) (y : upUniG K w.1.sum), F (a * x, y * b) = F (x, y) := by
    intro a ha b hb x y
    show Φ w.1.sum (orbZ w (a * x, y * b)) * phase ψ ((a * x, y * b) : lowW K w.1 w.2 × upUniG K w.1.sum) = _
    rw [inv_orbZ, inv_phase R ψ hψ w a ha b hb x y]
    congr 1
    exact h1 _ _ _ a.2.1 ha.1 b.2 hb.1
  have hFrep : ∀ p, F (rep R (toCos R p)) = F p := by
    intro p
    obtain ⟨a, ha, b, hb, e⟩ := inv_exists R p (rep R (toCos R p)) (inv_toCos_rep R _).symm
    rw [e]
    exact hFinv a ha b hb p.1 p.2
  have hfin : (Function.support (fun q : Cos R w => F (rep R q))).Finite := by
    refine (st_fin_cos hD w π).subset ?_
    intro q hq
    have h3 : Φ w.1.sum (orbZ w (rep R q)) ≠ 0 := left_ne_zero_of_mul hq
    exact h2 _ h3
  have s1 : ∑ᶠ q : Cos R w, F (rep R q) =
      ∑ᶠ q₂ : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum),
        ∑ᶠ q₁ : Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))),
          F (rep R ((q₁, q₂) : Cos R w)) := by
    rw [← finsum_comp_equiv (Equiv.prodComm (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))
      (Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))))]
    rw [finsum_curry]
    · rfl
    · exact hfin.preimage (Equiv.injective _).injOn
  show ∑ᶠ q : Cos R w, F (rep R q) = _
  rw [s1]
  refine finsum_congr fun (q₂ : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1))) => ?_
  symm
  refine finsum_eq_of_bijective _ (st_low_bij (R := R) m t c) fun ξ => ?_
  have e : ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w) =
      toCos R (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂) :=
    Prod.ext rfl (Quotient.out_eq q₂).symm
  show _ = F (rep R ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w))
  rw [e, hFrep]
  show _ = Φ w.1.sum (orbZ w (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂)) *
    phase ψ ((sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂) :
      lowW K w.1 w.2 × upUniG K w.1.sum)
  rw [st_orbZ_low, st_phase_low]
  show _ = Φ (m + 1) (blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (outV R ξ ᵥ* antidiagonalBlock m t) (c : K) *
    sec_m (Quotient.out q₂)) * ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q₂)))
  rw [st_blk_Hm m t (c : K) (outV R ξ) _ (Quotient.out q₂).2]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
