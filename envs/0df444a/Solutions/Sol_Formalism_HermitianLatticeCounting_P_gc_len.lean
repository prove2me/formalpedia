-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gc_len
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:49.81669+00:00
-- url     : https://prove2.me/submissions/f253389e-ed42-4c85-b8b2-198fbbe8c4de

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {l : ℕ} (y : Fin l → V) (a : Fin l) :
    majorantDistance y a = ‖gramSchmidt ℂ y a‖ := by
  unfold majorantDistance
  set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK
  have hKeq : K = Submodule.span ℂ (gramSchmidt ℂ y '' Set.Iio a) := by
    rw [span_gramSchmidt_Iio]; rfl
  set v : V := y a - gramSchmidt ℂ y a with hv
  have hvK : v ∈ K := by
    rw [hKeq, hv]
    conv => enter [2, 1]; rw [gramSchmidt_def'' ℂ y a]
    rw [add_sub_cancel_left]
    refine Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨b, Finset.mem_Iio.1 hb, rfl⟩
  have huv : y a - v = gramSchmidt ℂ y a := by rw [hv]; abel
  have horth : ∀ w ∈ K, inner ℂ (y a - v) w = 0 := by
    intro w hw
    rw [huv]
    rw [hKeq] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact gramSchmidt_orthogonal ℂ y (ne_of_gt hb)
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have := (K.norm_eq_iInf_iff_inner_eq_zero hvK).2 horth
  rw [huv] at this
  rw [this, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
end Formalism.HermitianLatticeCounting.P
