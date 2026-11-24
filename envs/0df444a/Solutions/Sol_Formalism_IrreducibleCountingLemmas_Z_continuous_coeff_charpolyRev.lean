-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.continuous_coeff_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:47.312502+00:00
-- url     : https://prove2.me/submissions/430318b2-9027-4d6c-93cb-5a3750a352c5

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ContinuousCoeffCharpolyRev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z
section
variable {G R : Type} [TopologicalSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
private theorem CoeffCont.const (p : R[X]) : CoeffCont (fun _ : G => p) := by
  intro j
  exact continuous_const
private theorem CoeffCont.mul {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g * Q g := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact continuous_finset_sum _ fun x _ => (hP x.1).mul (hQ x.2)
private theorem CoeffCont.sub {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g - Q g := by
  intro j
  simp only [Polynomial.coeff_sub]
  exact (hP j).sub (hQ j)
private theorem CoeffCont.sum {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∑ i ∈ s, P i g := by
  intro j
  simp only [Polynomial.finset_sum_coeff]
  exact continuous_finset_sum _ fun i hi => hP i hi j
private theorem CoeffCont.prod {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∏ i ∈ s, P i g := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using CoeffCont.const (G := G) (1 : R[X])
  · intro a s ha ih hP
    have h1 := hP a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    have h3 := CoeffCont.mul h1 h2
    simpa only [Finset.prod_insert ha] using h3
private theorem CoeffCont.C {f : G → R} (hf : Continuous f) :
    CoeffCont fun g => Polynomial.C (f g) := by
  intro j
  by_cases h : j = 0
  · subst h
    simpa using hf
  · simpa [Polynomial.coeff_C, h] using (continuous_const : Continuous fun _ : G => (0 : R))
end
end Formalism.IrreducibleCountingLemmas.Z
end

set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
variable {G R : Type} [TopologicalSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution {n : ℕ} {r : G → Matrix (Fin n) (Fin n) R}
    (hr : Continuous r) (j : ℕ) : Continuous fun g => (Matrix.charpolyRev (r g)).coeff j := by
  have hsmul : ∀ (u : ℤˣ) {Q : G → R[X]}, CoeffCont Q → CoeffCont fun g => u • Q g := by
    intro u Q hQ j
    simp only [Units.smul_def, Polynomial.coeff_smul]
    exact (hQ j).const_smul (u : ℤ)
  have h : CoeffCont fun g => Matrix.charpolyRev (r g) := by
    simp only [Matrix.charpolyRev, Matrix.det_apply]
    refine CoeffCont.sum _ fun σ _ => ?_
    refine hsmul _ (CoeffCont.prod _ fun i _ => ?_)
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact CoeffCont.sub (CoeffCont.const _) (CoeffCont.mul (CoeffCont.const _) (CoeffCont.C (hr.matrix_elem _ _)))
  exact h j
end Formalism.IrreducibleCountingLemmas.Z
