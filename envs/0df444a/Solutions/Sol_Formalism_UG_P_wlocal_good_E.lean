-- Prove2me | solution 1 for Formalism.UG.P.wlocal_good_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:20.297806+00:00
-- url     : https://prove2.me/submissions/2718a686-bfb6-4847-af58-8d8df921a567

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_eval_rowGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.UG.P
open Formalism.GradedWeylDivisibility
section
variable {R : Type} [CommRing R]
private lemma coeff_rowGen_mem_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    (rowGen R a b f).coeff k ∈ weyl R r n hn ν := by
  unfold weyl at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    unfold weyl
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ hx hy
  · intro m x _ hx
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ m hx
end
section
variable {R : Type} [CommRing R]
end
section
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
end
section
variable {R S : Type} [CommRing R] [CommRing S]
end
section
variable {R : Type} [CommRing R]
end
end Formalism.UG.P
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (c : R) :
    wlocal_Good hn ν (wlocal_E a b c) := by
  intro f hf
  rw [← wlocal_eval_rowGen, Polynomial.eval_eq_sum_range]
  apply Submodule.sum_mem
  intro k _
  rw [← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (coeff_rowGen_mem_weyl hn ν b a k f hf)
end Formalism.UG.P
