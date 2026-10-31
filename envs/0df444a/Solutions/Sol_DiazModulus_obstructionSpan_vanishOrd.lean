-- Prove2me | solution 1 for DiazModulus.obstructionSpan_vanishOrd
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:01:09.271401+00:00
-- url     : https://prove2.me/submissions/68a4a118-e456-4ae9-a8a7-a4a06a9cd1f5

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusDeriv_mem_torusBox
import Theorems.Thm_DiazModulus_torusDeriv_torusTransl
import Theorems.Thm_DiazModulus_vanishOrd_ideal
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # The obstruction span lies in the box and vanishes to order `M₀` on `Σ · S`

Box: a generator of `F` is `σ_{g_s v}(D_l P)`; `D_l P` stays in the box `D` (O1, iterated along `l`) and the
translation `σ_{g_s v}` is a `ℂ`-algebra automorphism mapping the box onto itself (V2).

Vanishing: `vanishOrd J W M₀` is (the carrier of) an ideal containing `J₀` whenever `J₀ ≤ J` (O6), and
`J₀ ≤ I(Σ · S)` because `Y_i Z_i − 1` vanishes at every `(x, y, y⁻¹)`. So it suffices that every generator
`Q = σ_{g_s v}(D_l P)` (`|s_j| ≤ r M₁`, `v ∈ Z(𝔭)`, `l` a `W`-list of length `≤ r M₀`) vanishes to order `M₀`.
For a `W`-list `l'` of length `≤ M₀`, `D_{l'} Q = σ_{g_s v}(D_{l' ++ l} P)` (O2, iterated), and its value at
`g_{s'} γ` (`|s'_j| ≤ M₁`, `γ ∈ S`) is the value of `σ_{g_{s + s'}}(D_{l' ++ l} P)` at `v γ` (`g_{s+s'} = g_s g_{s'}`,
the group is commutative). Now `|s + s'| ≤ (r+1) M₁` and `|l' ++ l| ≤ (r+1) M₀`, so this translate lies in `𝔭` by
`hb`, and `v γ ∈ Z(𝔭)` by `hS`: the value is `0`. -/

namespace C13_Z2
open DiazModulus MvPolynomial

theorem hmePoint_add {A₀ A₁ B₁ : Type*} [Fintype B₁] (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ)
    (s s' : B₁ → ℤ) : hmePoint u a (s + s') = hmePoint u a s * hmePoint u a s' := by
  refine Prod.ext ?_ ?_
  · show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
    simp [add_smul, Finset.sum_add_distrib]
  · funext i
    simp [hmePoint, zpow_add, Finset.prod_mul_distrib]

theorem torusDerivList_cons {A₀ A₁ : Type*} (w : (A₀ → ℂ) × (A₁ → ℂ)) (l : List ((A₀ → ℂ) × (A₁ → ℂ)))
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :
    torusDerivList (w :: l) f = torusDeriv w (torusDerivList l f) := by
  simp [torusDerivList, Module.End.mul_apply]

theorem torusDerivList_append {A₀ A₁ : Type*} (l' l : List ((A₀ → ℂ) × (A₁ → ℂ)))
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :
    torusDerivList (l' ++ l) f = torusDerivList l' (torusDerivList l f) := by
  simp [torusDerivList, List.map_append, List.prod_append, Module.End.mul_apply]

theorem torusDerivList_torusTransl {A₀ A₁ : Type*} (l : List ((A₀ → ℂ) × (A₁ → ℂ)))
    (g : TorusGroup ℂ A₀ A₁) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :
    torusDerivList l (torusTransl g f) = torusTransl g (torusDerivList l f) := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [torusDerivList_cons, torusDerivList_cons, ih, torusDeriv_torusTransl]

theorem torusDerivList_mem_torusBox {A₀ A₁ : Type*} (l : List ((A₀ → ℂ) × (A₁ → ℂ)))
    (T : A₀ ⊕ A₁ → ℕ) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hf : f ∈ torusBox ℂ A₀ A₁ T) :
    torusDerivList l f ∈ torusBox ℂ A₀ A₁ T := by
  induction l with
  | nil => exact hf
  | cons w l ih => rw [torusDerivList_cons]; exact (torusDeriv_mem_torusBox w).1 T _ ih

theorem torusIdeal_le_torusVanishing {A₀ A₁ : Type*} (S : Set (TorusGroup ℂ A₀ A₁)) :
    torusIdeal ℂ A₀ A₁ ≤ torusVanishing S := by
  rw [torusIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp [torusVanishing, torusPt, torusPoint]

end C13_Z2

open DiazModulus C13_Z2 in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype B₁] (D₀ D₁ : ℕ) (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)
    (hP : P ∈ torusBox ℂ A₀ A₁ (boxD A₀ A₁ D₀ D₁)) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (u : B₁ → A₀ → ℂ)
    (a : B₁ → A₁ → ℂˣ) (M₀ M₁ r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (hb : ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((r + 1) * M₁ : ℕ) : ℤ)) → ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (r + 1) * M₀ →
        (∀ w ∈ l, w ∈ W) → torusTransl (hmePoint u a s) (torusDerivList l P) ∈ 𝔭)
    (S : Set (TorusGroup ℂ A₀ A₁)) (hS : ∀ v ∈ torusZero 𝔭, ∀ γ ∈ S, v * γ ∈ torusZero 𝔭) :
    obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) ≤ torusBox ℂ A₀ A₁ (boxD A₀ A₁ D₀ D₁) ∧
      ((torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd (torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ S, z = hmePoint u a s * γ}) W M₀ := by
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, hs, v, hv, l, hl, hW, rfl⟩
    obtain ⟨⟨e, he, hbox, -⟩, -⟩ := torusTransl_algEquiv (hmePoint u a s * v)
    have hmem := Submodule.mem_map_of_mem (f := e.toLinearMap)
      (torusDerivList_mem_torusBox l _ P hP)
    rw [hbox] at hmem
    simpa [he] using hmem
  · set Jv := torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ S,
      z = hmePoint u a s * γ}
    obtain ⟨I, hIeq, hJI⟩ := vanishOrd_ideal Jv W M₀
    rw [← hIeq]
    refine SetLike.coe_subset_coe.mpr (sup_le (hJI (torusIdeal_le_torusVanishing _)) ?_)
    have hle : obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) ≤ I.restrictScalars ℂ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨s, hs, v, hv, l, hl, hW, rfl⟩
      show _ ∈ (I : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
      rw [hIeq]
      intro l' hl' hW'
      rw [torusDerivList_torusTransl, ← torusDerivList_append]
      simp only [Jv, torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
      rintro _ ⟨s', hs', γ, hγ, rfl⟩
      rw [eval_torusTransl]
      have hmem := hb (s + s') (fun b => by
          have h1 := abs_add_le (s b) (s' b)
          have h2 := hs b
          have h3 := hs' b
          push_cast at h2 ⊢
          simp only [Pi.add_apply]
          nlinarith) (l' ++ l)
        (by rw [List.length_append, Nat.succ_mul]; omega)
        (fun w hw => (List.mem_append.mp hw).elim (hW' w) (hW w))
      have h0 := hS v hv γ hγ _ hmem
      rw [eval_torusTransl, hmePoint_add] at h0
      rw [show hmePoint u a s' * γ * (hmePoint u a s * v) = v * γ * (hmePoint u a s * hmePoint u a s')
        by ac_rfl]
      exact h0
    rw [Ideal.span_le]
    exact fun x hx => hle hx
