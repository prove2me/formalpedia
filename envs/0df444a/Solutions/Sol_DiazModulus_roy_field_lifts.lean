-- Prove2me | solution 1 for DiazModulus.roy_field_lifts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:22.401423+00:00
-- url     : https://prove2.me/submissions/5d99fcfe-aa2d-4a31-bff5-91c212d1819f

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The number field of the coefficients and the lifts `η`
Write each coordinate `z_{i,j} ∈ ℒ̃` as a finite sum `Σ_l f_l g_l` with `f_l ∈ Q̄` and
`g_l ∈ {1} ∪ ℒ` (`Submodule.mem_span_set'`). Let `k = ℚ(all f_l)`, a number field
(`IntermediateField.finiteDimensional_adjoin`), and let `ω` be a ℚ-basis of `k`; so `m ≥ 1`,
`ω` is ℚ-free and algebraic, and `span_ℚ ω = k` contains `1` and the products `ω_a ω_b`.
`ℒ` is a ℚ-vector space: it contains `0`, is closed under addition (`exp` turns sums into
products), and under rational multiples, since `exp(r g)^{den r} = exp(g)^{num r}` and a
number whose power is algebraic is algebraic. For `c ∈ k` and `g ∈ {1} ∪ ℒ` the product
`c g` has the shape `u + Σ_k ω_k v_k` with `u ∈ k` and `v_k ∈ ℒ`: take `u = c, v = 0` if
`g = 1`, and otherwise expand `c = Σ_k r_k ω_k` and take `u = 0`, `v_k = r_k g`. The shape
survives finite sums. Applied to `ω_a z_{i,j} = Σ_l (ω_a f_l) g_l`, with `ω_a f_l ∈ k`, this
gives `x` and `y` with `ω_a z_{i,j} = x_j + Σ_c ω_c y_{(c,j)}`, and `η_{(a,i)} = (x, y)`
satisfies `Υ(η_{(a,i)}) = ω_a z_i`. -/

namespace RC1_FL
open DiazModulus

theorem logAlg_add {u v : ℂ} (hu : u ∈ LogAlg) (hv : v ∈ LogAlg) : u + v ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (u + v))
  rw [Complex.exp_add]
  exact mem_Qbar_iff.mp (Qbar.mul_mem (mem_Qbar_iff.mpr hu) (mem_Qbar_iff.mpr hv))

theorem logAlg_zero : (0 : ℂ) ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp 0)
  rw [Complex.exp_zero]
  exact isAlgebraic_one

theorem logAlg_ratMul {g : ℂ} (hg : g ∈ LogAlg) (r : ℚ) : (r : ℂ) * g ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp ((r : ℂ) * g))
  have h1 : Complex.exp ((r : ℂ) * g) ^ r.den = Complex.exp g ^ r.num := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul]
    congr 1
    have hd : (r.den : ℂ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [Rat.cast_def]
    field_simp
  have h2 : Complex.exp g ^ r.num ∈ Qbar := zpow_mem (mem_Qbar_iff.mpr hg) _
  exact IsAlgebraic.of_pow r.den_pos (h1 ▸ mem_Qbar_iff.mp h2)

/-- Coordinates of `c ∈ K` in the basis `Module.finBasis ℚ K`. -/
theorem rep (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {c : ℂ} (hc : c ∈ K) :
    c = ∑ k, (((Module.finBasis ℚ K).repr ⟨c, hc⟩ k : ℚ) : ℂ) *
      ((Module.finBasis ℚ K k : K) : ℂ) := by
  have h := congrArg (fun w : K => (w : ℂ)) ((Module.finBasis ℚ K).sum_repr ⟨c, hc⟩)
  simp only [IntermediateField.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl (fun k _ => ?_))
  rw [IntermediateField.coe_smul, Rat.smul_def]

theorem mem_span_of_mem (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {c : ℂ}
    (hc : c ∈ K) :
    c ∈ Submodule.span ℚ (Set.range fun k => ((Module.finBasis ℚ K k : K) : ℂ)) := by
  rw [rep K hc]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Rat.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The shape `u + Σ_k ω_k v_k`, `u ∈ K`, `v_k ∈ ℒ`. -/
def Shape (K : IntermediateField ℚ ℂ) {m : ℕ} (ω : Fin m → ℂ) (w : ℂ) : Prop :=
  ∃ u ∈ K, ∃ v : Fin m → ℂ, (∀ k, v k ∈ LogAlg) ∧ w = u + ∑ k, ω k * v k

theorem shape_zero (K : IntermediateField ℚ ℂ) {m : ℕ} (ω : Fin m → ℂ) : Shape K ω 0 :=
  ⟨0, K.zero_mem, 0, fun _ => logAlg_zero, by simp⟩

theorem shape_add (K : IntermediateField ℚ ℂ) {m : ℕ} (ω : Fin m → ℂ) {w w' : ℂ}
    (hw : Shape K ω w) (hw' : Shape K ω w') : Shape K ω (w + w') := by
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  obtain ⟨u', hu', v', hv', rfl⟩ := hw'
  refine ⟨u + u', K.add_mem hu hu', v + v', fun k => logAlg_add (hv k) (hv' k), ?_⟩
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem shape_term (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {c g : ℂ} (hc : c ∈ K)
    (hg : g ∈ insert (1 : ℂ) LogAlg) :
    Shape K (fun k => ((Module.finBasis ℚ K k : K) : ℂ)) (c * g) := by
  rcases hg with rfl | hg
  · exact ⟨c, hc, 0, fun _ => logAlg_zero, by simp⟩
  · refine ⟨0, K.zero_mem, fun k => (((Module.finBasis ℚ K).repr ⟨c, hc⟩ k : ℚ) : ℂ) * g,
      fun k => logAlg_ratMul hg _, ?_⟩
    refine (congrArg (· * g) (rep K hc)).trans ?_
    rw [zero_add, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)

end RC1_FL

open DiazModulus RC1_FL in
theorem solution {d ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hz : ∀ i j, z i j ∈ LogAlgTilde) :
    ∃ (m : ℕ) (ω : Fin m → ℂ) (η : Fin m × Fin ℓ → (Fin d → ℂ) × (Fin m × Fin d → ℂ)),
      0 < m ∧ LinearIndependent ℚ ω ∧ (∀ a, ω a ∈ Qbar) ∧
      (1 : ℂ) ∈ Submodule.span ℚ (Set.range ω) ∧
      (∀ a b, ω a * ω b ∈ Submodule.span ℚ (Set.range ω)) ∧
      (∀ p, (∀ i, (η p).1 i ∈ Submodule.span ℚ (Set.range ω)) ∧ ∀ q, (η p).2 q ∈ LogAlg) ∧
      ∀ p, (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) (η p) = ω p.1 • z p.2 := by
  choose n f g hfg using fun ij : Fin ℓ × Fin d => Submodule.mem_span_set'.mp (hz ij.1 ij.2)
  set S : Set ℂ :=
    Set.range (fun p : (Σ ij : Fin ℓ × Fin d, Fin (n ij)) => ((f p.1 p.2 : Qbar) : ℂ))
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
  have hkey : ∀ (a : Fin (Module.finrank ℚ K)) (i : Fin ℓ) (j : Fin d),
      Shape K ω (ω a * z i j) := by
    intro a i j
    rw [← hfg (i, j), Finset.mul_sum]
    refine Finset.sum_induction _ (Shape K ω) (fun _ _ => shape_add K ω) (shape_zero K ω) ?_
    intro l _
    rw [Subfield.smul_def, smul_eq_mul, ← mul_assoc]
    have hfK : ((f (i, j) l : Qbar) : ℂ) ∈ K :=
      IntermediateField.subset_adjoin _ _ ⟨⟨(i, j), l⟩, rfl⟩
    exact shape_term K (K.mul_mem (Module.finBasis ℚ K a).2 hfK) (g (i, j) l).2
  choose U hU V hV hUV using hkey
  refine ⟨Module.finrank ℚ K, ω, fun p => (fun j => U p.1 p.2 j, fun kj => V p.1 p.2 kj.2 kj.1),
    Module.finrank_pos, ?_, fun a => hK _ (Module.finBasis ℚ K a).2,
    mem_span_of_mem K K.one_mem,
    fun a b => mem_span_of_mem K (K.mul_mem (Module.finBasis ℚ K a).2 (Module.finBasis ℚ K b).2),
    fun p => ⟨fun j => mem_span_of_mem K (hU _ _ _), fun kj => hV _ _ _ _⟩, ?_⟩
  · exact (Module.finBasis ℚ K).linearIndependent.map' K.val.toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  · rintro ⟨a, i⟩
    funext j
    simp only [LinearMap.pi_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_fst, LinearMap.coe_snd, LinearMap.coe_proj, Function.eval,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply]
    exact (hUV a i j).symm
