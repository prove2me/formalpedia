-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallD.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:21.111826+00:00
-- url     : https://prove2.me/submissions/7551faf2-1642-4a4f-9f20-7b4f19845972

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallD_emb_injective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallD_psi_emb
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_forall_embedding_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_mem_ell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallD
open BallB BallC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}
namespace Formalism.HermitianLattices.Ext.L3.BallD
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ∀ x : V, (j : ℝ)⁻¹ • emb b x ∈ ballSet h b ↔
      ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ (j : ℝ) ^ 2 := by
    intro x
    rw [forall_embedding_iff hK b ho x]
    simp only [ballSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ell,
      map_smul]
    refine forall_congr' fun w => ?_
    have h1 : ∀ i, Complex.normSq (((j : ℝ)⁻¹ • psi K (Fin (finrank K V)) (emb b x)) w i) =
        ((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i)) := by
      intro i
      rw [Pi.smul_apply, Pi.smul_apply, psi_emb, Complex.real_smul, map_mul, Complex.normSq_ofReal]
      field_simp
    simp only [h1]
    have h2 : ∑ i, (w.1.embedding (h (b i) (b i))).re *
        (((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i))) =
        (∑ i, (w.1.embedding (h (b i) (b i))).re *
          Complex.normSq (w.1.embedding (b.repr x i))) / (j : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, div_le_one (by positivity)]
  unfold ballCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(j : ℝ)⁻¹ • emb b x.1, (key x.1).2 x.2.2,
      Set.smul_mem_smul_set ⟨x.1, x.2.1, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : (j : ℝ)⁻¹ • emb b x.1 = (j : ℝ)⁻¹ • emb b y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (emb_injective b (smul_right_injective _ (inv_ne_zero hj'.ne') h1))
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy2
    exact ⟨⟨x, hx, (key x).1 hy1⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.BallD
