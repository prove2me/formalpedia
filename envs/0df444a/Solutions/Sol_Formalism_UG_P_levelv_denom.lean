-- Prove2me | solution 1 for Formalism.UG.P.levelv_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:02.326797+00:00
-- url     : https://prove2.me/submissions/3cd7e948-4b2b-42a5-8507-d457a156d8db

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_tmul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (y : E ⊗[F] v.adicCompletion F) : ∃ N : ℕ, N ≠ 0 ∧ N • y ∈ lvS F E v := by
  classical
  have h1 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = (m • e) ⊗ₜ[F] x :=
    fun m e x => (map_nsmul ((TensorProduct.mk F E (v.adicCompletion F)).flip x) m e).symm
  have h2 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = e ⊗ₜ[F] (m • x) :=
    fun m e x => (map_nsmul (TensorProduct.mk F E (v.adicCompletion F) e) m x).symm
  have hE : ∀ e : E, ∃ M : ℕ, M ≠ 0 ∧ M • e ∈ intOE E := by
    intro e
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
    refine ⟨Ideal.absNorm (Ideal.span {s}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hs0
    · refine RingHom.mem_range.mpr ⟨t * a, ?_⟩
      have hs' : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 E) E), ← ht, map_mul, map_mul]
      field_simp <;> ring
  have hF : ∀ x : v.adicCompletion F, ∃ N : ℕ, N ≠ 0 ∧ N • x ∈ v.adicCompletionIntegers F := by
    intro x
    obtain ⟨b, hb, hbx⟩ :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    · have hcv : algebraMap (𝓞 F) (v.adicCompletion F) c ∈ v.adicCompletionIntegers F :=
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) c).2
      have key : Ideal.absNorm (Ideal.span {b}) • x = algebraMap (𝓞 F) (v.adicCompletion F) c *
          (x * algebraMap (𝓞 F) (v.adicCompletion F) b) := by
        rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)), ← hc, map_mul]
        ring
      rw [key]
      exact mul_mem hcv hbx
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | tmul e x =>
    obtain ⟨M, hM0, hM⟩ := hE e
    obtain ⟨N, hN0, hN⟩ := hF x
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [mul_smul, h2, h1]
    exact levelv_tmul_mem v _ hM _ hN
  | add y z hy hz =>
    obtain ⟨M, hM0, hM⟩ := hy
    obtain ⟨N, hN0, hN⟩ := hz
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hM _
    · rw [mul_smul]
      exact nsmul_mem hN _
end Formalism.UG.P
