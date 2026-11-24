-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.T_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:46:57.706744+00:00
-- url     : https://prove2.me/submissions/c3c5b696-2ca1-4ca2-b480-75a5c48cae02

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
    (hb : ∀ i, b i ∈ I.L)
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : I.fmat x *ᵥ iv I (b i) ∈ I.Lf := by
  have hsub : Lw I w ≤ I.Lf := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have hyL : y ∈ I.L := by
      refine (Submodule.span_le.mpr ?_) hy
      rintro _ ⟨a, _, z, hz, rfl⟩
      rw [show ((a : 𝓞 I.E) : I.E) • z = a • z from algebraMap_smul I.E a z]
      exact I.L.smul_mem a hz
    exact Submodule.subset_span ⟨⟨y, hyL⟩, rfl⟩
  have hmem : ∀ j, iv I (b j) ∈ I.Lf := fun j => Submodule.subset_span ⟨⟨b j, hb j⟩, rfl⟩
  have hS : (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) ∈ I.Lf :=
    sum_mem (fun j _ => by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hmem j) _)
  have h := add_mem (hsub (hM i)) hS
  rwa [sub_add_cancel] at h
end Formalism.L2.SG.Pf.RedConj0Pf
