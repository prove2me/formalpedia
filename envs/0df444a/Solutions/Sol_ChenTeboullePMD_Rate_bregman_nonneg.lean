-- Prove2me | solution 1 for ChenTeboullePMD.Rate.bregman_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T10:21:24.442032+00:00
-- url     : https://prove2.me/submissions/2e899897-43d1-4eb1-817a-71f2d96e257c

-- Direction: Alexander Richard Towell (queelius); completion and verification: OpenAI Codex.
-- Mathematics: Gong Chen and Marc Teboulle; platform: mikedeng1, reviewed by Shuze Chen.
-- Adapted supporting-hyperplane and midpoint strategy from carlok's failed attempts
-- 7eb849f5-0f75-4b53-af35-8c528261f8b0 and 8984fb19-2d76-43d7-b305-8031ba1e931c.
import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting
open ChenTeboullePMD.Rate BeckTeboulleMD.EMDA Filter Topology Set
namespace BregmanResearch
lemma support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {ψ : E → ℝ} (hc : ConvexOn ℝ S ψ) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S) (hd : DifferentiableAt ℝ ψ y) :
    fderiv ℝ ψ y (x-y) ≤ ψ x-ψ y := by
  have hpath : HasDerivAt (fun t : ℝ => y+t • (x-y)) (x-y) 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id' (0 : ℝ)).smul_const (x-y)) using 1
    · funext t
      rfl
    · simp
  have hline : HasDerivAt (fun t : ℝ => ψ (y+t • (x-y))) (fderiv ℝ ψ y (x-y)) 0 := by
    have hf : HasFDerivAt ψ (fderiv ℝ ψ y) (y+(0 : ℝ) • (x-y)) := by simpa using hd.hasFDerivAt
    exact hf.comp_hasDerivAt 0 hpath
  have ht : Tendsto (fun t : ℝ => (ψ (y+t • (x-y))-ψ y)/t)
      (𝓝[>] 0) (𝓝 (fderiv ℝ ψ y (x-y))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hline.tendsto_slope_zero.mono_left (nhdsWithin_mono _ (show Ioi (0 : ℝ) ⊆ {0}ᶜ by intro t ht; simp only [mem_compl_iff,mem_singleton_iff]; exact ne_of_gt ht))
  apply le_of_tendsto ht
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have he : y+t • (x-y)=(1-t) • y+t • x := by module
  have hj := hc.2 hy hx (sub_nonneg.mpr ht.2) ht.1.le (by ring : (1-t)+t=1)
  rw [← he] at hj
  simp only [smul_eq_mul] at hj
  exact (div_le_iff₀ ht.1).mpr (by nlinarith)
end BregmanResearch

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ) :
    ∀ x ∈ closure S, ∀ y ∈ S,
      0 ≤ bregman ψ x y ∧ (bregman ψ x y=0 ↔ x=y) := by
  intro x hx y hy
  have hyc : y ∈ closure S := subset_closure hy
  have hd : DifferentiableAt ℝ ψ y :=
    (hψ.contDiffOn.contDiffAt (hψ.isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hs := BregmanResearch.support hψ.strictConvexOn.convexOn hx hyc hd
  constructor
  · unfold bregman; linarith
  constructor
  · intro he
    by_contra hn
    have hm : (1/2 : ℝ) • y+(1/2 : ℝ) • x ∈ closure S :=
      hψ.strictConvexOn.1 hyc hx (by norm_num) (by norm_num) (by norm_num)
    have hb := BregmanResearch.support hψ.strictConvexOn.convexOn hm hyc hd
    have hstrict := hψ.strictConvexOn.2 hyc hx (Ne.symm hn)
      (show (0 : ℝ) < 1/2 by norm_num) (show (0 : ℝ) < 1/2 by norm_num) (by norm_num : (1/2 : ℝ)+1/2=1)
    have hv : (1/2 : ℝ) • y+(1/2 : ℝ) • x-y=(1/2 : ℝ) • (x-y) := by module
    rw [hv,map_smul] at hb
    simp only [smul_eq_mul] at hb hstrict
    unfold bregman at he
    linarith
  · rintro rfl
    simp [bregman]
