-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pol_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:34.80769+00:00
-- url     : https://prove2.me/submissions/0405a617-9f2b-40d7-8612-2dcc6c39a985

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} (LL : Letters N) : FiniteDimensional ℚ_[p] (Pol p r LL) := by
  classical
  let bnd : Fin N × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LL.total)
  have hfin : ({m | MultiDeg LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite := by
    refine (Set.finite_Iic bnd).subset ?_
    intro m hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro a
    have h1 : m a ≤ ∑ c, m (a.1, c) :=
      Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
    have h2 : LL.deg a.1 ≤ LL.total :=
      Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
    have h3 : bnd a = LL.total := by simp [bnd]
    rw [h3]
    rw [hm a.1] at h1
    omega
  have hle : Pol p r LL ≤ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p])) ''
      {m | MultiDeg LL m}) := by
    intro x hx
    rw [Pol, mem_restrictSupport_iff] at hx
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have : monomial m (x.coeff m) = x.coeff m • (monomial m (1 : ℚ_[p])) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hx (Finset.mem_coe.mpr hm), rfl⟩)
  have : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) :
      MvPolynomial (Fin N × Fin r) ℚ_[p])) '' {m | MultiDeg LL m})) :=
    FiniteDimensional.span_of_finite ℚ_[p] (hfin.image _)
  exact Submodule.finiteDimensional_of_le hle
end Formalism.CountingSumsFrames
