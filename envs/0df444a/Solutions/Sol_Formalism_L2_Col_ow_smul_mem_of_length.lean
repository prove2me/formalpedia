-- Prove2me | solution 1 for Formalism.L2.Col.ow_smul_mem_of_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:19.76213+00:00
-- url     : https://prove2.me/submissions/417756c2-cc94-4d46-b206-88ecc549ba67

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_exists_pow_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]
namespace Formalism.L2.Col
theorem _root_.solution (hQ : Module.length (Ow w) Q ≠ ⊤) (N : Submodule (𝓞 K) Q) (r : Ow w)
    {x : Q} (hx : x ∈ N) : r • x ∈ N := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero w Q hQ x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
  obtain ⟨y, i, hi, hyi⟩ := w.isMaximal.exists_inv s.2
  have hcop : IsCoprime (s : 𝓞 K) (i ^ n) := IsCoprime.pow_right ⟨y, 1, by rw [one_mul]; exact hyi⟩
  obtain ⟨b, c, hbc⟩ := hcop
  have h0 : (c * i ^ n) • x = 0 := hn _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hi n))
  have h1 : x = (s : 𝓞 K) • (b • x) := by
    conv_lhs => rw [← one_smul (𝓞 K) x, ← hbc, add_smul, h0, add_zero, mul_comm, mul_smul]
  have h2 : IsLocalization.mk' (Ow w) a s • x = a • (b • x) := by
    conv_lhs => rw [h1]
    rw [← algebraMap_smul (Ow w) (s : 𝓞 K), smul_smul, IsLocalization.mk'_spec, algebraMap_smul]
  rw [h2]
  exact N.smul_mem a (N.smul_mem b hx)
end Formalism.L2.Col
