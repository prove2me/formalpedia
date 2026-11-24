-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.gram_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:32.003228+00:00
-- url     : https://prove2.me/submissions/c51ef7e5-756a-4f6a-b0f2-1d6d67226ec7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_form_rel
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (a b : Fin m → V) (e : Fin m → K) (γ : K)
    (hab : ∀ i, γ • b i = e i • a i) :
    (star γ * γ) ^ m * (Matrix.of fun i j => h (b i) (b j)).det =
      ((∏ i, star (e i)) * ∏ i, e i) * (Matrix.of fun i j => h (a i) (a j)).det := by
  have h1 : (star γ * γ) • (Matrix.of fun i j => h (b i) (b j)) =
      Matrix.diagonal (fun i => star (e i)) * (Matrix.of fun i j => h (a i) (a j)) *
        Matrix.diagonal e := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [form_rel h (hab i) (hab j)]
    ring
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Fintype.card_fin] at h2
  rw [h2]
  ring
end Formalism.HermitianLattices.Ext.L3.D2.J
