-- Prove2me | solution 1 for DiazModulus.roy_semistable_node
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:00:33.667872+00:00
-- url     : https://prove2.me/submissions/51ae8ffa-762e-4187-99a5-d653bb95187e

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_linear_subgroup_transcendence
import Theorems.Thm_DiazModulus_roy_field_lifts
import Theorems.Thm_DiazModulus_roy_upsilon_dims
import Theorems.Thm_DiazModulus_roy_intKer_image
import Theorems.Thm_DiazModulus_roy_relation_rank_le
import Theorems.Thm_DiazModulus_roy_period_space
import Theorems.Thm_DiazModulus_roy_rational_adapted_basis

open Complex ComplexConjugate

/-! # Lemma A: the semistable node
Let `z₁, …, z_ℓ` be a `Q̄`-basis of `Z₁ ⊂ U ∩ ℒ̃^d`, `n = dim U < d`, `U` semistable. `roy_field_lifts` gives a
number field `k = span_ℚ ω` and lifts `η ∈ k^d × ℒ^{md}` with `Υ(η_(b,i)) = ω_b z_i`. DALAG Th. 11.21 at
`V = Υ⁻¹(U)` (dimension `n + md` by `roy_upsilon_dims`), with the algebraic spanning family of `ker Υ`, returns
`(V', φ, L₁, ℓ_T)` with `(mℓ − ρ + md − l₁)(d − n) ≤ md(d* − ℓ_T)`; by `roy_upsilon_dims` `d* − ℓ_T = d − dim Υ(V'×L₁)`.
Put `T = Υ(span(V' ∩ Q̄^d) × L₁) = span(V' ∩ Q̄^d) ⊔ Υ₁(L₁)`: it is rational (`roy_intKer_image`), `t = dim T < d`,
and `l₁ ≤ m·t`, which gives `(mℓ − ρ)(d − n) ≤ mn(d − t)`. `roy_relation_rank_le` bounds `ρ ≤ m·dim F`,
`F = span z ⊓ (T + 2πi·Q̄^d)`; `roy_period_space` gives a rational `R` with `dim F + t ≤ dim(F ⊓ T) + dim R` and
`dim(U ⊓ R) + t = dim(U ⊓ T) + dim R`; semistability at `R` bounds `dim(U ⊓ R)`. Finally the induction hypothesis
at `t < d`, transported to `ℂ^t` by the adapted basis of `T` (`roy_rational_adapted_basis`), gives
`(d − n)·dim(span z ⊓ T) ≤ d·dim(U ⊓ T)`; adding these inequalities yields `(d − n)ℓ ≤ dn`. -/

namespace RC1_D
open DiazModulus

noncomputable def Ups (d m : ℕ) (ω : Fin m → ℂ) :
    ((Fin d → ℂ) × (Fin m × Fin d → ℂ)) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d =>
    (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)

noncomputable def Ups1 (d m : ℕ) (ω : Fin m → ℂ) : (Fin m × Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d => ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)

/-- The algebraic family spanning `ker Υ`. -/
def wfam (d m : ℕ) (ω : Fin m → ℂ) (p : Fin m × Fin d) : (Fin d → ℂ) × (Fin m × Fin d → ℂ) :=
  ((fun i => if i = p.2 then -ω p.1 else 0), (fun q => if q = p then (1 : ℂ) else 0))

/-- Rational subspaces: spanned by their algebraic vectors. -/
def IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S

theorem ups_eq (d m : ℕ) (ω : Fin m → ℂ) :
    Ups d m ω = LinearMap.coprod LinearMap.id (Ups1 d m ω) := by
  apply LinearMap.ext; rintro ⟨x, y⟩; funext i
  simp [Ups, Ups1]

theorem map_prod_ups (d m : ℕ) (ω : Fin m → ℂ) (A : Submodule ℂ (Fin d → ℂ))
    (L : Submodule ℂ (Fin m × Fin d → ℂ)) : (A.prod L).map (Ups d m ω) = A ⊔ L.map (Ups1 d m ω) := by
  rw [ups_eq, LinearMap.map_coprod_prod, Submodule.map_id]

theorem finrank_prod' {d m : ℕ} (A : Submodule ℂ (Fin d → ℂ)) (B : Submodule ℂ (Fin m × Fin d → ℂ)) :
    Module.finrank ℂ ↥(A.prod B) = Module.finrank ℂ ↥A + Module.finrank ℂ ↥B := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A.map (LinearMap.inl ℂ _ (Fin m × Fin d → ℂ)))
    (B.map (LinearMap.inr ℂ (Fin d → ℂ) _))
  rw [disjoint_iff.mp (LinearMap.disjoint_inl_inr.mono LinearMap.map_le_range LinearMap.map_le_range),
    finrank_bot, add_zero, ← LinearMap.prod_eq_sup_map] at h
  rw [h, ← (Submodule.equivMapOfInjective _ LinearMap.inl_injective A).finrank_eq,
    ← (Submodule.equivMapOfInjective _ LinearMap.inr_injective B).finrank_eq]

theorem isRat_span {d : ℕ} (V' : Submodule ℂ (Fin d → ℂ)) :
    IsRat (Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar}) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_mono fun _ hv => ⟨Submodule.subset_span hv, hv.2⟩)

theorem isRat_sup {d : ℕ} {A B : Submodule ℂ (Fin d → ℂ)} (hA : IsRat A) (hB : IsRat B) :
    IsRat (A ⊔ B) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (sup_le (le_trans (le_of_eq hA.symm) (Submodule.span_mono fun _ hv => ⟨Submodule.mem_sup_left hv.1, hv.2⟩))
      (le_trans (le_of_eq hB.symm) (Submodule.span_mono fun _ hv => ⟨Submodule.mem_sup_right hv.1, hv.2⟩)))

theorem mem_Qbar_of_span {m : ℕ} {ω : Fin m → ℂ} (hω : ∀ a, ω a ∈ Qbar) {x : ℂ}
    (hx : x ∈ Submodule.span ℚ (Set.range ω)) : x ∈ Qbar := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hω a
  | zero => exact Qbar.zero_mem
  | add _ _ _ _ h1 h2 => exact Qbar.add_mem h1 h2
  | smul q _ _ h => rw [Rat.smul_def]; exact Qbar.mul_mem (SubfieldClass.ratCast_mem Qbar q) h

/-- The final arithmetic (CRUX A3–A8). -/
theorem arith {m d n t ℓ ρ l₁ F FT r nT nR : ℕ}
    (hineq : (m * ℓ - ρ + (m * d - l₁)) * (d - n) ≤ m * d * (d - t))
    (hm : 0 < m) (hnd : n < d) (htd : t ≤ d) (hρ : ρ ≤ m * ℓ) (hl₁ : l₁ ≤ m * t)
    (hF : F + t ≤ FT + r) (hρF : ρ ≤ m * F) (hUR : nR + t = nT + r)
    (hssR : d * nR ≤ n * r) (hIH : (d - n) * FT ≤ d * nT) :
    (d - n) * ℓ ≤ d * n := by
  have hl₁d : l₁ ≤ m * d := hl₁.trans (Nat.mul_le_mul_left m htd)
  have key : m * ((d - n) * ℓ) ≤ m * (d * n) := by
    zify [hρ, hl₁d, hnd.le, htd] at hineq hIH hl₁ hρF hF hUR hssR ⊢
    rw [show (nR : ℤ) = nT + r - t by linarith] at hssR
    have hdn : (0 : ℤ) ≤ d - n := by linarith
    have hm' : (0 : ℤ) ≤ m := by positivity
    -- (T′) plus A5–A7, each multiplied out; the sum is exactly the goal
    linarith [mul_nonneg (sub_nonneg.mpr hl₁) hdn, mul_nonneg hdn (sub_nonneg.mpr hρF),
      mul_nonneg (mul_nonneg hm' hdn) (show (0 : ℤ) ≤ FT + r - F - t by linarith),
      mul_nonneg hm' (sub_nonneg.mpr hIH), mul_nonneg hm' (sub_nonneg.mpr hssR)]
  exact Nat.le_of_mul_le_mul_left key hm

theorem rank_le_card {m ℓ : ℕ} (s : Submodule ℚ (Fin m × Fin ℓ → ℚ)) : Module.finrank ℚ ↥s ≤ m * ℓ := by
  simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le s

theorem span_logAlg {d ℓ : ℕ} {z : Fin ℓ → Fin d → ℂ} (hz : ∀ i j, z i j ∈ LogAlgTilde) :
    ∀ x ∈ Submodule.span (↥Qbar) (Set.range z), ∀ j, x j ∈ LogAlgTilde := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hz i
  | zero => intro j; exact LogAlgTilde.zero_mem
  | add _ _ _ _ h1 h2 => intro j; exact LogAlgTilde.add_mem (h1 j) (h2 j)
  | smul a _ _ h => intro j; exact LogAlgTilde.smul_mem a (h j)

/-- Extension by zero `ℂ^t → ℂ^d`. -/
noncomputable def extZ (d t : ℕ) : (Fin t → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d => if h : i.val < t then LinearMap.proj ⟨i.val, h⟩ else 0

theorem extZ_apply {d t : ℕ} (w : Fin t → ℂ) (i : Fin d) :
    extZ d t w i = if h : i.val < t then w ⟨i.val, h⟩ else 0 := by
  unfold extZ; rw [LinearMap.pi_apply]; split_ifs <;> rfl

/-- CRUX A7: the induction hypothesis at `t = dim T < d`, moved inside the rational `T`. -/
theorem transport {d n : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ), Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥(S)) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ LogAlgTilde) → LinearIndependent (↥Qbar) z' →
        (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥(U'))
    (U T : Submodule ℂ (Fin d → ℂ)) (hnd : n < d) (hT : IsRat T) (htd : Module.finrank ℂ ↥T < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ), IsRat S → d * Module.finrank ℂ ↥(U ⊓ S) ≤ n * Module.finrank ℂ ↥S)
    (Z : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) ↥Z] (hZU : ∀ x ∈ Z, x ∈ U)
    (hZL : ∀ x ∈ Z, ∀ i, x i ∈ LogAlgTilde) :
    (d - n) * Module.finrank (↥Qbar) ↥(Z ⊓ T.restrictScalars (↥Qbar)) ≤ d * Module.finrank ℂ ↥(U ⊓ T) := by
  obtain ⟨g, galg, glog, gT⟩ := DiazModulus.roy_rational_adapted_basis T hT
  have htd' : Module.finrank ℂ ↥T ≤ d := htd.le
  let E : (Fin (Module.finrank ℂ ↥T) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := g.symm.toLinearMap ∘ₗ extZ d _
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ ↥T) → ℂ) :=
    (LinearMap.pi fun j => LinearMap.proj (Fin.castLE htd' j)) ∘ₗ g.toLinearMap
  have hgE : ∀ w, g (E w) = extZ d _ w := fun w => g.apply_symm_apply _
  have hPE : ∀ w, P (E w) = w := by
    intro w; funext j
    show g (E w) (Fin.castLE htd' j) = w j
    rw [hgE, extZ_apply]; split_ifs with h
    · rfl
    · exact absurd j.isLt h
  have hEinj : Function.Injective E := Function.LeftInverse.injective hPE
  have hET : ∀ w, E w ∈ T := fun w =>
    (gT (E w)).mpr fun i hi => by rw [hgE, extZ_apply, dif_neg (not_lt.mpr hi)]
  have hEP : ∀ v ∈ T, E (P v) = v := by
    intro v hv; apply g.injective; rw [hgE]; funext i; rw [extZ_apply]
    split_ifs with h
    · rfl
    · exact ((gT v).mp hv i (not_lt.mp h)).symm
  have hrange : LinearMap.range E = T :=
    le_antisymm (by rintro _ ⟨w, rfl⟩; exact hET w) (fun v hv => ⟨P v, hEP v hv⟩)
  have hfin : ∀ X : Submodule ℂ (Fin (Module.finrank ℂ ↥T) → ℂ),
      Module.finrank ℂ ↥(X.map E) = Module.finrank ℂ ↥X :=
    fun X => (Submodule.equivMapOfInjective E hEinj X).finrank_eq.symm
  have hU'map : (U.comap E).map E = U ⊓ T := by rw [Submodule.map_comap_eq, hrange, inf_comm]
  have : FiniteDimensional (↥Qbar) ↥(Z ⊓ T.restrictScalars (↥Qbar)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let b := Module.finBasis (↥Qbar) ↥(Z ⊓ T.restrictScalars (↥Qbar))
  have hbT : ∀ i, (b i : Fin d → ℂ) ∈ T := fun i => (Submodule.mem_inf.mp (b i).2).2
  have hbZ : ∀ i, (b i : Fin d → ℂ) ∈ Z := fun i => (Submodule.mem_inf.mp (b i).2).1
  have key := hIH _ htd (U.comap E) n d _ (fun i => P (b i)) hnd ?_ ?_ ?_ ?_
  · rwa [← hfin (U.comap E), hU'map] at key
  · intro S' hS'
    have hSrat : IsRat (S'.map E) := by
      apply le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
      calc S'.map E = (Submodule.span ℂ {v | v ∈ S' ∧ ∀ i, v i ∈ Qbar}).map E := by rw [hS']
        _ = Submodule.span ℂ (E '' {v | v ∈ S' ∧ ∀ i, v i ∈ Qbar}) := Submodule.map_span _ _
        _ ≤ _ := Submodule.span_mono (by
          rintro _ ⟨w, hw, rfl⟩
          refine ⟨Submodule.mem_map_of_mem hw.1, (galg (extZ d _ w) fun i => ?_).2⟩
          rw [extZ_apply]; split_ifs
          · exact hw.2 _
          · exact Qbar.zero_mem)
    have h1 : (U.comap E ⊓ S').map E = U ⊓ S'.map E := by
      have hST : S'.map E ≤ T := by rintro _ ⟨w, -, rfl⟩; exact hET w
      rw [Submodule.map_inf E hEinj, hU'map, inf_assoc, inf_eq_right.mpr hST]
    rw [← hfin (U.comap E ⊓ S'), ← hfin S', h1]
    exact hss _ hSrat
  · intro i; show E (P (b i)) ∈ U; rw [hEP _ (hbT i)]; exact hZU _ (hbZ i)
  · intro i j; exact (glog _ (hZL _ (hbZ i))).1 (Fin.castLE htd' j)
  · apply LinearIndependent.of_comp (E.restrictScalars (↥Qbar))
    have : (E.restrictScalars (↥Qbar)) ∘ (fun i => P (b i)) =
        (Z ⊓ T.restrictScalars (↥Qbar)).subtype ∘ b := funext fun i => hEP _ (hbT i)
    rw [this]
    exact b.linearIndependent.map' _ (Submodule.ker_subtype _)

end RC1_D

open DiazModulus RC1_D in
theorem solution (hME : MultiplicityEstimateElem) {d : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ), Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥(S)) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ LogAlgTilde) → LinearIndependent (↥Qbar) z' →
        (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥(U'))
    (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥(U) < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ), Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥(U) * Module.finrank ℂ ↥(S))
    {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    (d - Module.finrank ℂ ↥(U)) * ℓ ≤ d * Module.finrank ℂ ↥(U) := by
  -- A1: number field and lifts
  obtain ⟨m, ω, η, hm, hωQ, hωalg, hω1, hωmul, hη, hηΥ⟩ := DiazModulus.roy_field_lifts z hz
  have hηΥ' : ∀ p, Ups d m ω (η p) = ω p.1 • z p.2 := hηΥ
  have hdimV : Module.finrank ℂ ↥(U.comap (Ups d m ω)) = Module.finrank ℂ ↥U + m * d :=
    (DiazModulus.roy_upsilon_dims ω U ⊥).1
  have hspan : Submodule.span ℂ (Set.range (wfam d m ω)) = LinearMap.ker (Ups d m ω) :=
    (DiazModulus.roy_upsilon_dims ω U ⊥).2.1
  have hW : ∀ X, Module.finrank ℂ ↥(LinearMap.ker (Ups d m ω) ⊔ X) =
      m * d + Module.finrank ℂ ↥(X.map (Ups d m ω)) := fun X => (DiazModulus.roy_upsilon_dims ω U X).2.2
  have hmd : 1 ≤ m * d := Nat.mul_pos hm (by omega)
  have hdmd : d ≤ m * d := Nat.le_mul_of_pos_left d hm
  have hwK : ∀ k, wfam d m ω k ∈ LinearMap.ker (Ups d m ω) := fun k => hspan ▸ Submodule.subset_span ⟨k, rfl⟩
  -- A2: DALAG Th. 11.21
  obtain ⟨V', q, φ, L₁, ℓT, hL₁, hℓT, hℓlt, hineq⟩ :=
    DiazModulus.linear_subgroup_transcendence hME (ι₀ := Fin d) (ι₁ := Fin m × Fin d)
      (κ₀ := Fin m × Fin d) (κ₁ := Fin m × Fin ℓ) (U.comap (Ups d m ω))
      (by rw [hdimV]; omega) (by simp only [hdimV, Fintype.card_prod, Fintype.card_fin]; omega)
      (by simp only [hdimV, Fintype.card_fin]; omega) (wfam d m ω)
      (fun k => LinearMap.ker_le_comap _ (hwK k)) (fun k => ⟨fun h => by simp only [wfam]; split_ifs; exacts [Qbar.neg_mem (hωalg _), Qbar.zero_mem],
        fun i => by simp only [wfam]; split_ifs; exacts [Qbar.one_mem, Qbar.zero_mem]⟩)
      η (fun p => by rw [Submodule.mem_comap, hηΥ']; exact U.smul_mem _ (hzU _))
      (fun p => ⟨fun h => mem_Qbar_of_span hωalg ((hη p).1 h), (hη p).2⟩)
  -- A3: d* − ℓ_T = d − dim Υ(V' × L₁)
  simp only [Fintype.card_prod, Fintype.card_fin, hdimV] at hℓlt hineq
  rw [hspan] at hℓT
  have hWdim : Module.finrank ℂ ↥(LinearMap.ker (Ups d m ω)) = m * d := by
    have h := hW ⊥; rwa [sup_bot_eq, Submodule.map_bot, finrank_bot, add_zero] at h
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (Ups d m ω)) (V'.prod L₁)
  have hX := finrank_prod' V' L₁
  have hWX := hW (V'.prod L₁)
  have hXd := Submodule.finrank_le ((V'.prod L₁).map (Ups d m ω))
  have hV'd := Submodule.finrank_le V'
  have hL₁d := Submodule.finrank_le L₁
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hXd hV'd hL₁d
  have hδ : d - Module.finrank ℂ ↥V' + (m * d - Module.finrank ℂ ↥L₁) - ℓT =
      d - Module.finrank ℂ ↥((V'.prod L₁).map (Ups d m ω)) := by omega
  have hdn : d + m * d - (Module.finrank ℂ ↥U + m * d) = d - Module.finrank ℂ ↥U := by omega
  rw [hδ, hdn] at hineq
  -- the rational space T = span(V' ∩ Q̄^d) ⊔ Υ₁(L₁), and A4
  set V₀ := Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar} with hV₀
  set T := (V₀.prod L₁).map (Ups d m ω) with hTdef
  have htX : Module.finrank ℂ ↥T ≤ Module.finrank ℂ ↥((V'.prod L₁).map (Ups d m ω)) :=
    Submodule.finrank_mono (Submodule.map_mono
      (Submodule.prod_mono (Submodule.span_le.mpr fun _ hv => hv.1) le_rfl))
  have htd : Module.finrank ℂ ↥T < d := by omega
  have hTeq : T = V₀ ⊔ L₁.map (Ups1 d m ω) := map_prod_ups d m ω V₀ L₁
  obtain ⟨hl₁, hL₁rat⟩ := DiazModulus.roy_intKer_image ω hωQ hωalg φ L₁ hL₁
  have hTrat : IsRat T := by rw [hTeq]; exact isRat_sup (isRat_span V') hL₁rat
  have hΥ1T : L₁.map (Ups1 d m ω) ≤ T := by rw [hTeq]; exact le_sup_right
  have hl₁t : Module.finrank ℂ ↥L₁ ≤ m * Module.finrank ℂ ↥T :=
    hl₁.trans (Nat.mul_le_mul_left m (Submodule.finrank_mono hΥ1T))
  have hineq' := hineq.trans (Nat.mul_le_mul_left (m * d) (Nat.sub_le_sub_left htX d))
  -- A5: the relation rank
  have hρ := DiazModulus.roy_relation_rank_le ω hωQ hωalg hω1 hωmul z hzind η (fun p i => (hη p).1 i)
    (fun p r => (hη p).2 r) hηΥ V' φ L₁ hL₁
  -- A6: the period space R
  set Z := Submodule.span (↥Qbar) (Set.range z) with hZdef
  have hZfin : FiniteDimensional (↥Qbar) ↥Z := FiniteDimensional.span_of_finite _ (Set.finite_range z)
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hcdef
  set F := Z ⊓ Submodule.span (↥Qbar)
    {x : Fin d → ℂ | ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + c • κ} with hFdef
  have hFfin : FiniteDimensional (↥Qbar) ↥F := Submodule.finiteDimensional_of_le inf_le_left
  have hZU : ∀ x ∈ Z, x ∈ U := fun x hx =>
    (Submodule.span_le (p := U.restrictScalars (↥Qbar))).mpr (by rintro _ ⟨i, rfl⟩; exact hzU i) hx
  have hset : ∀ x ∈ Submodule.span (↥Qbar)
      {x : Fin d → ℂ | ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + c • κ},
      ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + c • κ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, T.zero_mem, 0, fun _ => Qbar.zero_mem, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨τ, hτ, κ, hκ, rfl⟩ := h1; obtain ⟨τ', hτ', κ', hκ', rfl⟩ := h2
      exact ⟨τ + τ', T.add_mem hτ hτ', κ + κ', fun i => Qbar.add_mem (hκ i) (hκ' i),
        by rw [smul_add]; abel⟩
    | smul a y _ h =>
      obtain ⟨τ, hτ, κ, hκ, rfl⟩ := h
      exact ⟨a • τ, (T.restrictScalars (↥Qbar)).smul_mem a hτ, a • κ,
        fun i => by show (a : ℂ) * κ i ∈ Qbar; exact Qbar.mul_mem a.2 (hκ i),
        by rw [smul_add, smul_comm]⟩
  obtain ⟨hRrat, hFR, hUR⟩ := DiazModulus.roy_period_space c Complex.two_pi_I_ne_zero T U hTrat F hFfin
    (fun x hx => hZU x (Submodule.mem_inf.mp hx).1) (fun x hx => hset x (Submodule.mem_inf.mp hx).2)
  have hssR := hss _ hRrat
  -- A7: induction inside T
  have hFTZ : Module.finrank (↥Qbar) ↥(F ⊓ T.restrictScalars (↥Qbar)) ≤
      Module.finrank (↥Qbar) ↥(Z ⊓ T.restrictScalars (↥Qbar)) :=
    have := Submodule.finiteDimensional_of_le (inf_le_left : Z ⊓ T.restrictScalars (↥Qbar) ≤ Z)
    Submodule.finrank_mono (inf_le_inf_right _ inf_le_left)
  have hIHT := transport hIH U T hUd hTrat htd (fun S hS => hss S hS) Z hZU (span_logAlg hz)
  -- A8
  exact arith hineq' hm hUd htd.le (rank_le_card _) hl₁t hFR hρ hUR hssR
    ((Nat.mul_le_mul_left _ hFTZ).trans hIHT)
