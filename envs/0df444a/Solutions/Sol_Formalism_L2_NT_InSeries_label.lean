-- Prove2me | solution 1 for Formalism.L2.NT.InSeries.label
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:57.926258+00:00
-- url     : https://prove2.me/submissions/df521e64-258d-42b1-925b-2f0baa17959b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {g : ℕ} [Fact g.Prime]
namespace Formalism.L2.NT
namespace InSeries
theorem _root_.solution {teich : Formalism.CyclotomicNorms.Fbar g →* ℂ} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar g} {r : ℕ}
    {χ : GL (Fin r) (ZMod g) → ℂ} {f : (ZMod g)[X]} (hζ : IsGenSys ζ) (h : InSeries teich ζ χ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨m, c, χs, ks, hpos, hsum, hcusp, hprod, -⟩ := h
  subst hprod
  have hint : ∀ i, IsIntegral (ZMod g) (ζ (c i) ^ ks i) := fun i => Algebra.IsIntegral.isIntegral _
  have hmon : ∀ i ∈ (Finset.univ : Finset (Fin m)), (labCusp ζ (c i) (ks i)).Monic :=
    fun i _ => minpoly.monic (hint i)
  refine ⟨Polynomial.monic_prod_of_monic _ _ hmon, ?_, ?_⟩
  · rw [Polynomial.natDegree_prod_of_monic _ _ hmon, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hcusp i).2.2
  · rw [Polynomial.coeff_zero_prod, Finset.prod_ne_zero_iff]
    intro i _
    apply minpoly.coeff_zero_ne_zero (hint i)
    apply pow_ne_zero
    intro h0
    have ho := (hζ (c i) (hpos i)).1
    rw [h0] at ho
    have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
    have h1 : 1 ≤ g ^ c i - 1 := by
      have : 2 ≤ g ^ c i := le_trans hg (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (hpos i)) g)
      omega
    have hz : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
      rw [orderOf_eq_zero_iff']
      intro n hn
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
      exact zero_ne_one
    omega
end InSeries
end Formalism.L2.NT
