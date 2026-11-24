-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.red_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:47:01.797784+00:00
-- url     : https://prove2.me/submissions/df8e5512-be05-4e51-9355-a30dde567907

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b i)) =
      ∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j)) := by
  have hsum : (∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j))) =
      (Lw I w).mkQ (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [hsum]
  exact (Submodule.Quotient.eq _).mpr (hM i)
end Formalism.L2.SG.Pf.RedConj0Pf
