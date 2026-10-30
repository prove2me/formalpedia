-- Prove2me | solution 1 for DiazModulus.exists_sse_lifts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:10:29.091267+00:00
-- url     : https://prove2.me/submissions/6a388a20-e3ad-471f-926a-abbf440f6d27

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic

open Complex ComplexConjugate

/-! # Lifting the six products to `𝔾ₐ² × 𝔾ₘ^{2m}`

Write each `x_i y_j ∈ ℒ̃` as a finite sum `Σ_l f_l g_l` with `f_l ∈ Q̄` and `g_l ∈ {1} ∪ ℒ`
(`Submodule.mem_span_set'`). Let `K = ℚ(all f_l)`, a number field
(`IntermediateField.finiteDimensional_adjoin`), and let `ω` be a ℚ-basis of `K`; so `m ≥ 1`,
`ω` is ℚ-free and algebraic. For `c ∈ K` and `g ∈ {1} ∪ ℒ` the product `c g` has the shape
`u + Σ_k ω_k v_k` with `u ∈ Q̄` and `v_k ∈ ℒ`: take `u = c, v = 0` if `g = 1`, and otherwise
expand `c = Σ_k r_k ω_k` with `r_k ∈ ℚ` and take `u = 0`, `v_k = r_k g`, which lies in `ℒ` by
`Diaz.exp_ratMul_isAlgebraic`. Since `ℒ` contains `0` and is closed under addition
(`exp` turns sums into products of algebraic numbers), the shape survives finite sums. Applied
to `ω_a x_i y_j = Σ_l (ω_a f_l) g_l`, with `ω_a f_l ∈ K`, this gives `η_{(a,j)}` coordinatewise. -/

namespace C14_S1
open DiazModulus

theorem logAlg_add {u v : ℂ} (hu : u ∈ LogAlg) (hv : v ∈ LogAlg) : u + v ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (u + v))
  rw [Complex.exp_add]
  exact mem_Qbar_iff.mp (Qbar.mul_mem (mem_Qbar_iff.mpr hu) (mem_Qbar_iff.mpr hv))

theorem logAlg_zero : (0 : ℂ) ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp 0)
  rw [Complex.exp_zero]
  exact isAlgebraic_one

/-- The shape `u + Σ_k ω_k v_k`, `u ∈ Q̄`, `v_k ∈ ℒ`. -/
def Shape {m : ℕ} (ω : Fin m → ℂ) (z : ℂ) : Prop :=
  ∃ u ∈ Qbar, ∃ v : Fin m → ℂ, (∀ k, v k ∈ LogAlg) ∧ z = u + ∑ k, ω k * v k

theorem shape_zero {m : ℕ} (ω : Fin m → ℂ) : Shape ω 0 :=
  ⟨0, Qbar.zero_mem, 0, fun _ => logAlg_zero, by simp⟩

theorem shape_add {m : ℕ} (ω : Fin m → ℂ) {z w : ℂ} (hz : Shape ω z) (hw : Shape ω w) :
    Shape ω (z + w) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  obtain ⟨u', hu', v', hv', rfl⟩ := hw
  refine ⟨u + u', Qbar.add_mem hu hu', v + v', fun k => logAlg_add (hv k) (hv' k), ?_⟩
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem shape_term (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ c ∈ K, c ∈ Qbar) {c g : ℂ} (hc : c ∈ K) (hg : g ∈ insert (1 : ℂ) LogAlg) :
    Shape (fun k => ((Module.finBasis ℚ K k : K) : ℂ)) (c * g) := by
  rcases hg with rfl | hg
  · exact ⟨c, hK c hc, 0, fun _ => logAlg_zero, by simp⟩
  · set b := Module.finBasis ℚ K
    have hrep : c = ∑ k, ((b.repr ⟨c, hc⟩ k : ℚ) : ℂ) * ((b k : K) : ℂ) := by
      have h := congrArg (fun w : K => (w : ℂ)) (b.sum_repr ⟨c, hc⟩)
      simp only [IntermediateField.coe_sum] at h
      refine h.symm.trans (Finset.sum_congr rfl (fun k _ => ?_))
      rw [IntermediateField.coe_smul, Rat.smul_def]
    refine ⟨0, Qbar.zero_mem, fun k => ((b.repr ⟨c, hc⟩ k : ℚ) : ℂ) * g,
      fun k => Diaz.exp_ratMul_isAlgebraic hg _, ?_⟩
    refine (congrArg (· * g) hrep).trans ?_
    rw [zero_add, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)

end C14_S1

open DiazModulus C14_S1 in
theorem solution (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hxy : ∀ i j, x i * y j ∈ LogAlgTilde) :
    ∃ (m : ℕ) (ω : Fin m → ℂ) (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)),
      0 < m ∧ LinearIndependent ℚ ω ∧ (∀ a, ω a ∈ Qbar) ∧
      (∀ p, (∀ i, (η p).1 i ∈ Qbar) ∧ ∀ q, (η p).2 q ∈ LogAlg) ∧
      ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x := by
  choose n f g hfg using fun ij : Fin 2 × Fin 3 => Submodule.mem_span_set'.mp (hxy ij.1 ij.2)
  set S : Set ℂ := Set.range (fun p : (Σ ij : Fin 2 × Fin 3, Fin (n ij)) => ((f p.1 p.2 : Qbar) : ℂ))
  have hSQ : ∀ c ∈ S, c ∈ Qbar := by
    rintro _ ⟨p, rfl⟩
    exact (f p.1 p.2).2
  set K := IntermediateField.adjoin ℚ S
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun c hc => (mem_Qbar_iff.mp (hSQ c hc)).isIntegral)
  have hK : ∀ c ∈ K, c ∈ Qbar := fun c hc =>
    mem_Qbar_iff.mpr (IntermediateField.isAlgebraic_iff.mp
      (Algebra.IsAlgebraic.isAlgebraic (⟨c, hc⟩ : K)))
  set ω : Fin (Module.finrank ℚ K) → ℂ := fun k => ((Module.finBasis ℚ K k : K) : ℂ) with hω
  have hkey : ∀ (a : Fin (Module.finrank ℚ K)) (i : Fin 2) (j : Fin 3), Shape ω (ω a * (x i * y j)) := by
    intro a i j
    rw [← hfg (i, j), Finset.mul_sum]
    refine Finset.sum_induction _ (Shape ω) (fun _ _ => shape_add ω) (shape_zero ω) ?_
    intro l _
    rw [Subfield.smul_def, smul_eq_mul, ← mul_assoc]
    have hfK : ((f (i, j) l : Qbar) : ℂ) ∈ K :=
      IntermediateField.subset_adjoin _ _ ⟨⟨(i, j), l⟩, rfl⟩
    exact shape_term K hK (K.mul_mem (Module.finBasis ℚ K a).2 hfK) (g (i, j) l).2
  choose U hU V hV hUV using hkey
  refine ⟨Module.finrank ℚ K, ω, fun p => (fun i => U p.1 i p.2, fun ki => V p.1 ki.2 p.2 ki.1),
    Module.finrank_pos, ?_, fun a => hK _ (Module.finBasis ℚ K a).2, fun p => ⟨fun i => hU _ _ _, fun ki => hV _ _ _ _⟩, ?_⟩
  · exact (Module.finBasis ℚ K).linearIndependent.map' K.val.toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  · rintro ⟨a, j⟩
    funext i
    simp only [LinearMap.pi_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_fst, LinearMap.coe_snd, LinearMap.coe_proj, Function.eval, 
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply]
    rw [← mul_comm (x i), ← mul_assoc, mul_comm (x i), mul_assoc, hUV a i j]
