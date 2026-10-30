-- Prove2me | solution 1 for DiazModulus.restrictSupport_block_filtration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:24.111339+00:00
-- url     : https://prove2.me/submissions/24599a08-3ba9-45c5-93f9-c4e7746b6f88

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Block boxes form a multiplicative, finite-dimensional, exhaustive filtration

The block box `blockBox K β T` is `restrictSupport` of the set `S_T` of exponents `m` with
`(m.mapDomain β) b ≤ T b` for every block `b`.

* Multiplicative: `restrictSupport_add` gives `f * g ∈ restrictSupport (S_T + S_T')`, and
  `S_T + S_T' ⊆ S_{T + T'}` because `mapDomain β` is additive (`Finsupp.mapDomain_add`).
* Finite-dimensional: every `m ∈ S_T` satisfies `m s ≤ (m.mapDomain β) (β s) ≤ T (β s)` (split `m`
  as `single s (m s) + m.erase s`), so `S_T` lies in the interval `Iic M` of `σ →₀ ℕ`, which is
  finite since `σ` is finite; `basisRestrictSupport` is then a finite basis.
* Exhaustive: take `T b = Σ_{m ∈ supp f} (m.mapDomain β) b`; each exponent of `f` is bounded by
  the sum (`Finset.single_le_sum`). -/

namespace C11_T1
open DiazModulus

theorem le_mapDomain {σ ι : Type*} (β : σ → ι) (m : σ →₀ ℕ) (s : σ) :
    m s ≤ m.mapDomain β (β s) := by
  conv_rhs => rw [← Finsupp.single_add_erase s m]
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply,
    Finsupp.single_eq_same]
  exact Nat.le_add_right _ _

theorem finite_box {σ ι : Type*} [Finite σ] (β : σ → ι) (T : ι → ℕ) :
    Set.Finite {m : σ →₀ ℕ | ∀ b, m.mapDomain β b ≤ T b} := by
  classical
  have := Fintype.ofFinite σ
  let M : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => T (β s)
  refine (Set.finite_Iic M).subset ?_
  intro m hm s
  show m s ≤ T (β s)
  exact (le_mapDomain β m s).trans (hm (β s))

open scoped Pointwise in
theorem mul_mem_box {K σ ι : Type*} [Field K] (β : σ → ι) (T T' : ι → ℕ)
    (f g : MvPolynomial σ K) (hf : f ∈ blockBox K β T) (hg : g ∈ blockBox K β T') :
    f * g ∈ blockBox K β (T + T') := by
  have hfg : f * g ∈ MvPolynomial.restrictSupport K
      ({m : σ →₀ ℕ | ∀ b, m.mapDomain β b ≤ T b} +
        {m : σ →₀ ℕ | ∀ b, m.mapDomain β b ≤ T' b}) := by
    rw [MvPolynomial.restrictSupport_add]
    exact Submodule.mul_mem_mul hf hg
  refine MvPolynomial.restrictSupport_mono K ?_ hfg
  rintro _ ⟨m, hm, m', hm', rfl⟩ b
  rw [Finsupp.mapDomain_add, Finsupp.add_apply, Pi.add_apply]
  exact Nat.add_le_add (hm b) (hm' b)

end C11_T1

open DiazModulus C11_T1 in
theorem solution {K σ ι : Type*} [Field K] [Finite σ] (β : σ → ι) :
    (∀ (T T' : ι → ℕ) (f g : MvPolynomial σ K), f ∈ blockBox K β T → g ∈ blockBox K β T' →
        f * g ∈ blockBox K β (T + T')) ∧
      (∀ T : ι → ℕ, FiniteDimensional K ↥(blockBox K β T)) ∧
      ∀ f : MvPolynomial σ K, ∃ T : ι → ℕ, f ∈ blockBox K β T := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact fun T T' f g hf hg => mul_mem_box β T T' f g hf hg
  · intro T
    have := (finite_box β T).to_subtype
    exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K _)
  · intro f
    refine ⟨fun b => ∑ m ∈ f.support, m.mapDomain β b, ?_⟩
    rw [blockBox, MvPolynomial.mem_restrictSupport_iff]
    intro m hm b
    exact Finset.single_le_sum (f := fun m : σ →₀ ℕ => m.mapDomain β b)
      (fun _ _ => Nat.zero_le _) hm
