-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.secondOrder_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:45.738027+00:00
-- url     : https://prove2.me/submissions/60b4be4b-a227-4d77-a996-4bd650a0eeb9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_pderiv_comm
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_colSum_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (hPsi : PsiCoverSt H)
    (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) :
    TB.secondOrder S (fun p p' : Lt1 Dw × Fin n => if p.2 = p'.2 then
      dotProduct (Pi.single (ltIdx Dw p.1) 1) (β.mulVec (Pi.single (ltIdx Dw p'.1) 1)) +
      dotProduct (Pi.single (ltIdx Dw p'.1) 1) (β.mulVec (Pi.single (ltIdx Dw p.1) 1)) else 0)
      (MvPolynomial.map (algebraMap c.F S) (encP P)) = 0 := by
  classical
  set Q := MvPolynomial.map (algebraMap c.F S) (encP P) with hQ
  have hcol : ∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    intro ℓ ℓ' h
    simp only [hQ, MvPolynomial.pderiv_map]
    rw [← map_sum, colSum_conj c hPsi a n P hP ℓ ℓ' h, map_zero]
  have hcol' : ∀ ℓ ℓ' : Lt1 Dw, ℓ.1 = ComplexEmbedding.conjugate ℓ'.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    intro ℓ ℓ' h
    rw [Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) Q]
    exact hcol ℓ' ℓ h
  have hdot : ∀ i j, dotProduct (Pi.single i 1) (β.mulVec (Pi.single j 1)) = β i j := by
    intro i j
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  unfold TB.secondOrder
  simp only [hdot, Fintype.sum_prod_type, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ' _ => ?_
  rw [← Finset.mul_sum, map_add, add_mul]
  have h1 : MvPolynomial.C (β (ltIdx Dw ℓ) (ltIdx Dw ℓ')) *
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    by_cases hb : β (ltIdx Dw ℓ) (ltIdx Dw ℓ') = 0
    · rw [hb, map_zero, zero_mul]
    · rw [hcol ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]
  have h2 : MvPolynomial.C (β (ltIdx Dw ℓ') (ltIdx Dw ℓ)) *
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    by_cases hb : β (ltIdx Dw ℓ') (ltIdx Dw ℓ) = 0
    · rw [hb, map_zero, zero_mul]
    · rw [hcol' ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]
  rw [h1, h2, add_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
