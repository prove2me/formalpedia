-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.colSum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:55.054896+00:00
-- url     : https://prove2.me/submissions/9044c66a-31c3-4cbb-808e-42da1b46bc60

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_conj_conj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_pderiv_comm
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndEncPf_colSum_zero


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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hPsi : PsiCoverSt H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (ℓ ℓ' : Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (hℓ : ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) :
    ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) (encP P)) = 0 := by
  classical
  have hinj : Function.Injective (ltEquiv Dw n) := (ltEquiv Dw n).injective
  have hgen : ∀ ℓ ℓ' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), InPsi H ℓ.1 →
      ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) (encP P)) = 0 := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ hτ h
    simp only at h hτ
    subst h
    have key := CIndEncPf.colSum_zero c a n P hP τ hτ i i'
    calc ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i⟩, b)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i'⟩, b) (encP P))
        = ∑ b : Fin n, MvPolynomial.rename (ltEquiv Dw n) (MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
            (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          unfold encP
          rw [show ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) =
              ltEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i', b⟩ from rfl,
            MvPolynomial.pderiv_rename hinj,
            show ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) = ltEquiv Dw n ⟨τ, i, b⟩ from rfl,
            MvPolynomial.pderiv_rename hinj]
      _ = 0 := by rw [← map_sum, key, map_zero]
  rcases hPsi ℓ.1 with h1 | h1
  · exact hgen ℓ ℓ' h1 hℓ
  · have h2 := hgen ℓ' ℓ (by rw [hℓ]; exact h1) (by rw [hℓ, conj_conj])
    rw [Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) (encP P)]
    exact h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
