-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.mem_mmR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:01.588897+00:00
-- url     : https://prove2.me/submissions/eadf7b81-19c1-4eb0-9916-628b3de64ac2

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_coe_lift_intermediate
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_mem_mmR_of
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_fractional_ideal_span_top
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_fractional_ideal_dual_family
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_trace_dual_of_functional
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_sum_emb_dualBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (v : ι → M) :
    v ∈ mmR M emb I ↔
      ∀ b ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range := by
  refine ⟨mem_mmR_of K E φ₀ M ι emb hinj hres hcard hM I hI v, fun hv => ?_⟩
  obtain ⟨i0⟩ : Nonempty ι := by rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hφ : ∀ y, φ₀ y ∈ M := fun y => by rw [← hres i0 y]; exact hM i0 _
  let ψ : ι → E →+* M := fun i => (emb i).codRestrict M (hM i)
  let φM : K →+* M := φ₀.codRestrict M hφ
  have hψ : ∀ i y, liftM M (emb i y) = ψ i y := fun i y =>
    Subtype.ext (by rw [coe_lift_intermediate (hM i y)]; rfl)
  have hψK : ∀ i (t : K) (y : E), ψ i (t • y) = φM t * ψ i y := fun i t y => by
    rw [Algebra.smul_def, map_mul]; congr 1; exact Subtype.ext (hres i t)
  set P := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K ((I : Submodule (𝓞 E) E) : Set E)
  let e : Module.Basis s K E := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, fractional_ideal_span_top K E I hI])
  letI : Fintype s := @Fintype.ofFinite _ (Module.Finite.finite_basis e)
  have he : ∀ l, e l ∈ P := fun l => by rw [Module.Basis.mk_apply]; exact hs l.2
  obtain ⟨n, g, f, hg, hfg⟩ := fractional_ideal_dual_family K E I
  choose b hb using fun j => trace_dual_of_functional K E P e he (f j)
  have hbd : ∀ j, b j ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) :=
    fun j => (FractionalIdeal.mem_dual hI).mpr fun a ha => ⟨f j ⟨a, ha⟩, (hb j a ha).symm⟩
  have hid : ∀ y (hy : y ∈ P), y = ∑ j, Algebra.traceForm K E (b j) y • g j := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : P) : E) from rfl, hfg ⟨y, hy⟩]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j y hy, algebraMap_smul]
  set e' := (Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e with he'
  have hbexp : ∀ j, b j = ∑ l, Algebra.traceForm K E (b j) (e l) • e' l := fun j => by
    conv_lhs => rw [← e'.sum_repr (b j)]
    simp [e']
  have key : ∀ i k, ∑ j, ψ i (b j) * ψ k (g j) = if k = i then 1 else 0 := by
    intro i k
    have hdb := sum_emb_dualBasis K E φ₀ M ι emb hinj hres hcard hM e k i
    simp only [hψ, ← he'] at hdb
    rw [← hdb]
    have h1 : ∀ l, ψ k (e l) = ∑ j, φM (Algebra.traceForm K E (b j) (e l)) * ψ k (g j) := fun l => by
      conv_lhs => rw [hid (e l) (he l)]
      rw [map_sum]; simp only [hψK]
    have h2 : ∀ j, ψ i (b j) = ∑ l, φM (Algebra.traceForm K E (b j) (e l)) * ψ i (e' l) := fun j => by
      conv_lhs => rw [hbexp j]
      rw [map_sum]; simp only [hψK]
    simp only [h1, h2, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  choose c hc using fun j => RingHom.mem_range.mp (hv (b j) (hbd j))
  have hv' : v = ∑ j, c j • (fun i => liftM M (emb i (g j))) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, hc, hψ, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, key]
    simp
  rw [hv']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g j, hg j, rfl⟩)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
