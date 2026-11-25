-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.clear_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:31:55.538064+00:00
-- url     : https://prove2.me/submissions/054c097c-e7f0-41e2-9362-0033e8c1ffd3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaF_int_mem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_clear_F
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
namespace Formalism.L2.SG.Pf.PCountEx
section Clear
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
private theorem ιF_mem_O_of_mem_integers (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Fp)
    (hw : w ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) : algebraMap (A p).Fp (A p).Ep w ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have e : algebraMap (A p).Fp (A p).Ep w = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hw⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap
private theorem algebraMap_ιF_mem_O (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have hm := iotaF_int_mem A p t
  have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) =
      algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap
end Clear
section Mat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}
end Mat
end Formalism.L2.SG.Pf.PCountEx
end
end

set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (z : (A p).Ep) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) * z ∈ (A p).O := by
  haveI := (A p).lf
  have hz : z ∈ Submodule.span (A p).Fp (Set.range (A p).ιE) := by
    rw [(A p).span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    have hz : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
    have inj : ∀ x : ℤ, algebraMap ℤ E x = 0 → x = 0 := fun x hx => by simpa using hx
    have hint : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by
      first
      | (obtain ⟨⟨w, hw⟩, y, hy0, hyw⟩ := exists_integral_multiple hz inj
         refine ⟨y, hy0, ?_⟩
         rw [mul_comm]
         have hw' : IsIntegral ℤ w := hw
         simpa [hyw] using hw')
      | (obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
         exact ⟨y, hy0, by simpa [zsmul_eq_mul] using hy⟩)
    obtain ⟨y, hy0, hy⟩ := hint
    refine ⟨(y : 𝓞 F), by exact_mod_cast hy0, ?_⟩
    rw [← (A p).compat, ← map_mul]
    have e1 : algebraMap F E (algebraMap (𝓞 F) F (y : 𝓞 F)) * e = (y : E) * e := by simp
    rw [e1, (A p).O_def]
    have h2 : IsIntegral ℤ ((A p).ιE ((y : E) * e)) := hy.map (A p).ιE.toIntAlgHom
    exact h2.tower_top
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [mul_zero]
    exact Subring.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := hy
    refine ⟨t1 * t2, mul_ne_zero h10 h20, ?_⟩
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t1 * t2))) * (x + y) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) +
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) * y) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t2) h1)
      (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t1) h2)
  | smul c x _ hx =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := clear_F A p c
    refine ⟨t2 * t1, mul_ne_zero h20 h10, ?_⟩
    rw [Algebra.smul_def]
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t2 * t1))) *
        (algebraMap (A p).Fp (A p).Ep c * x) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2) * c) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.mul_mem _ (ιF_mem_O_of_mem_integers A p _ h2) h1
end Formalism.L2.SG.Pf.PCountEx
