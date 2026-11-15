-- Prove2me | solution 1 for DiazModulus.roy_rat_semistable_node
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:38:40.515696+00:00
-- url     : https://prove2.me/submissions/ec12f209-e6a7-4dbd-80de-73a926dded20

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_linear_subgroup_transcendence
import Theorems.Thm_DiazModulus_ratLogAlg_mem_iff
import Theorems.Thm_DiazModulus_roy_rat_adapted_basis
import Theorems.Thm_DiazModulus_roy_rat_relation_rank_le
import Theorems.Thm_DiazModulus_roy_rat_period_space

open Complex ComplexConjugate

/-! # Lemma A over ℚ: the semistable node
Let `n = dim U < d`, with `d·dim(U ∩ S) ≤ n·dim S` for every rational `S`, and let `z₁, …, z_ℓ` be ℚ-free in
`U ∩ (ℚ + ℒ)^d`. Write `z_j = b_j + λ_j` with `b_j ∈ ℚ^d` and `λ_j ∈ ℒ^d`. The map `Υ(x, y) = x + y` is onto, its
kernel is spanned by the vectors `(−e_h, e_h)`, so `V = Υ⁻¹(U)` has dimension `n + d` and
`dim(ker Υ + X) = d + dim Υ(X)`. The linear subgroup theorem at `V`, with that algebraic family and the lifts
`(b_j, λ_j)`, returns `V′`, an integer matrix with kernel `L₁` and an integer `ℓ_T`; the dimension count turns its
inequality into `(ℓ − ρ + d − l₁)(d − n) ≤ d(d − dim(V′ + L₁))`, with `dim(V′ + L₁) < d`. The space
`T = span(V′ ∩ ℚ^d) + L₁` is rational (the kernel of an integer matrix is spanned by rational vectors), `t = dim T < d`
and `l₁ ≤ t`. The relation rank `ρ` is at most `dim_ℚ F`, `F = span_ℚ z ∩ (T + 2πi·ℚ^d)`; the period space
`R = T + span F` is rational, with `dim F + t ≤ dim(F ∩ T) + dim R` and `dim(U ∩ R) + t = dim(U ∩ T) + dim R`, and
semistability at `R` bounds `dim(U ∩ R)`. The induction hypothesis at `t < d`, moved into `ℂ^t` by a rational adapted
basis of `T`, gives `(d − n)·dim(span z ∩ T) ≤ d·dim(U ∩ T)`. Adding these inequalities gives `(d − n)ℓ ≤ dn`. -/

namespace RC5_Q4
open DiazModulus

/-- `Υ(x, y) = x + y`. -/
noncomputable def Ups (d : ℕ) : ((Fin d → ℂ) × (Fin d → ℂ)) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.coprod LinearMap.id LinearMap.id

theorem Ups_apply {d : ℕ} (x : (Fin d → ℂ) × (Fin d → ℂ)) : Ups d x = x.1 + x.2 := by
  simp [Ups]

/-- The algebraic family `(−e_h, e_h)` spanning `ker Υ`. -/
def wfam (d : ℕ) (h : Fin d) : (Fin d → ℂ) × (Fin d → ℂ) :=
  ((fun i => if i = h then -1 else 0), (fun i => if i = h then 1 else 0))

/-- Rational subspaces: spanned by their rational vectors. -/
def IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S

theorem finrank_comap {d : ℕ} (U : Submodule ℂ (Fin d → ℂ)) :
    Module.finrank ℂ ↥(U.comap (Ups d)) = Module.finrank ℂ ↥U + d := by
  set f := U.mkQ ∘ₗ Ups d
  have hker : LinearMap.ker f = U.comap (Ups d) := by simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = ⊤ := by
    have : LinearMap.range (Ups d) = ⊤ :=
      LinearMap.range_eq_top.mpr fun u => ⟨(u, 0), by simp [Ups_apply]⟩
    simp only [f, LinearMap.range_comp, this, Submodule.map_top, Submodule.range_mkQ]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_quotient_add_finrank U
  have h3 : Module.finrank ℂ ((Fin d → ℂ) × (Fin d → ℂ)) = d + d := by
    simp [Module.finrank_prod]
  have h4 : Module.finrank ℂ (Fin d → ℂ) = d := by simp
  rw [hrange, finrank_top, hker, h3] at h1
  omega

theorem span_wfam (d : ℕ) : Submodule.span ℂ (Set.range (wfam d)) = LinearMap.ker (Ups d) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Ups_apply]
    funext i
    simp only [wfam, Pi.add_apply, Pi.zero_apply]
    split_ifs <;> norm_num
  · intro x hx
    rw [LinearMap.mem_ker, Ups_apply] at hx
    have hx1 : ∀ i, x.1 i = -x.2 i := fun i => by
      have := congrFun hx i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      linear_combination this
    have hsum : x = ∑ h, x.2 h • wfam d h := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [hx1 i, Prod.fst_sum, Finset.sum_apply]; simp [wfam]
      · rw [Prod.snd_sum, Finset.sum_apply]; simp [wfam]
    rw [hsum]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem finrank_ker_sup {d : ℕ} (X : Submodule ℂ ((Fin d → ℂ) × (Fin d → ℂ))) :
    Module.finrank ℂ ↥(LinearMap.ker (Ups d) ⊔ X) = d + Module.finrank ℂ ↥(X.map (Ups d)) := by
  rw [sup_comm, ← Submodule.comap_map_eq, finrank_comap, add_comm]

theorem map_prod_ups {d : ℕ} (A B : Submodule ℂ (Fin d → ℂ)) : (A.prod B).map (Ups d) = A ⊔ B := by
  rw [Ups, LinearMap.map_coprod_prod, Submodule.map_id, Submodule.map_id]

theorem finrank_prod' {d : ℕ} (A B : Submodule ℂ (Fin d → ℂ)) :
    Module.finrank ℂ ↥(A.prod B) = Module.finrank ℂ ↥A + Module.finrank ℂ ↥B := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A.map (LinearMap.inl ℂ _ (Fin d → ℂ)))
    (B.map (LinearMap.inr ℂ (Fin d → ℂ) _))
  rw [disjoint_iff.mp (LinearMap.disjoint_inl_inr.mono LinearMap.map_le_range LinearMap.map_le_range),
    finrank_bot, add_zero, ← LinearMap.prod_eq_sup_map] at h
  rw [h, ← (Submodule.equivMapOfInjective _ LinearMap.inl_injective A).finrank_eq,
    ← (Submodule.equivMapOfInjective _ LinearMap.inr_injective B).finrank_eq]

theorem isRat_span {d : ℕ} (V' : Submodule ℂ (Fin d → ℂ)) :
    IsRat (Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)}) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_mono fun _ hv => ⟨Submodule.subset_span hv, hv.2⟩)

theorem isRat_sup {d : ℕ} {A B : Submodule ℂ (Fin d → ℂ)} (hA : IsRat A) (hB : IsRat B) :
    IsRat (A ⊔ B) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (sup_le (le_trans (le_of_eq hA.symm) (Submodule.span_mono fun _ hv => ⟨Submodule.mem_sup_left hv.1, hv.2⟩))
      (le_trans (le_of_eq hB.symm) (Submodule.span_mono fun _ hv => ⟨Submodule.mem_sup_right hv.1, hv.2⟩)))

/-- The kernel of an integer matrix is spanned by its rational vectors. -/
theorem L1_rat {d q : ℕ} (φ : Fin q → Fin d → ℤ) (L₁ : Submodule ℂ (Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) : IsRat L₁ := by
  refine le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1) fun y hy => ?_
  have hy' := (hL₁ y).mp hy
  set C := Submodule.span ℚ (Set.range y)
  have : FiniteDimensional ℚ C := FiniteDimensional.span_of_finite ℚ (Set.finite_range y)
  set c := Module.finBasis ℚ C
  set e := c.equivFun
  let yC : Fin d → C := fun i => ⟨y i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hsum0 : ∀ k, ∑ i, (φ k i : ℚ) • yC i = 0 := by
    intro k
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, yC, Rat.smul_def,
      Rat.cast_intCast]
    exact hy' k
  have hr : ∀ t, (fun i => ((e (yC i) t : ℚ) : ℂ)) ∈
      {v : Fin d → ℂ | v ∈ L₁ ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} := by
    intro t
    refine ⟨(hL₁ _).mpr fun k => ?_, fun i => ⟨_, rfl⟩⟩
    have h2 : ∑ i, (φ k i : ℚ) * e (yC i) t = 0 := by
      have := congrArg (fun x => e x t) (hsum0 k)
      simpa [map_sum, map_smul] using this
    exact_mod_cast h2
  have hyexp : y = ∑ t, ((c t : C) : ℂ) • (fun i => ((e (yC i) t : ℚ) : ℂ)) := by
    funext i
    have := congrArg Subtype.val (c.sum_equivFun (yC i))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, yC] at this
    rw [Finset.sum_apply]
    refine this.symm.trans (Finset.sum_congr rfl fun t _ => ?_)
    simp [e, yC, mul_comm]
  rw [hyexp]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span (hr t))

/-- The final arithmetic (A3 and A8). -/
theorem arith {d n t ℓ ρ l₁ F FT r nT nR : ℕ}
    (hineq : (ℓ - ρ + (d - l₁)) * (d - n) ≤ d * (d - t))
    (hnd : n < d) (htd : t ≤ d) (hρ : ρ ≤ ℓ) (hl₁ : l₁ ≤ t)
    (hF : F + t ≤ FT + r) (hρF : ρ ≤ F) (hUR : nR + t = nT + r)
    (hssR : d * nR ≤ n * r) (hIH : (d - n) * FT ≤ d * nT) :
    (d - n) * ℓ ≤ d * n := by
  have hl₁d : l₁ ≤ d := hl₁.trans htd
  have hnd' : (n : ℤ) < d := by exact_mod_cast hnd
  zify [hρ, hl₁d, hnd.le, htd] at hineq hIH hl₁ hρF hF hUR hssR ⊢
  rw [show (nR : ℤ) = nT + r - t by linarith] at hssR
  have hdn : (0 : ℤ) ≤ d - n := by linarith
  linarith [mul_nonneg (sub_nonneg.mpr hl₁) hdn, mul_nonneg hdn (sub_nonneg.mpr hρF),
    mul_nonneg hdn (show (0 : ℤ) ≤ FT + r - F - t by linarith)]

theorem rank_le_card {ℓ : ℕ} (s : Submodule ℚ (Fin ℓ → ℚ)) : Module.finrank ℚ ↥s ≤ ℓ := by
  simpa using Submodule.finrank_le s

theorem span_coord {d ℓ : ℕ} {z : Fin ℓ → Fin d → ℂ} (M : Submodule ℚ ℂ) (hz : ∀ i j, z i j ∈ M) :
    ∀ x ∈ Submodule.span ℚ (Set.range z), ∀ j, x j ∈ M := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hz i
  | zero => intro j; exact M.zero_mem
  | add _ _ _ _ h1 h2 => intro j; exact M.add_mem (h1 j) (h2 j)
  | smul a _ _ h => intro j; exact M.smul_mem a (h j)

theorem isQ_iff (x : ℂ) : (∃ q : ℚ, x = (q : ℂ)) ↔ x ∈ Submodule.span ℚ {(1 : ℂ)} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩

/-- Extension by zero `ℂ^t → ℂ^d`. -/
noncomputable def extZ (d t : ℕ) : (Fin t → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d => if h : i.val < t then LinearMap.proj ⟨i.val, h⟩ else 0

theorem extZ_apply {d t : ℕ} (w : Fin t → ℂ) (i : Fin d) :
    extZ d t w i = if h : i.val < t then w ⟨i.val, h⟩ else 0 := by
  unfold extZ; rw [LinearMap.pi_apply]; split_ifs <;> rfl

/-- A7: the induction hypothesis at `t = dim T < d`, moved inside the rational `T`. -/
theorem transport {d n : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ),
          Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
        LinearIndependent ℚ z' → (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥U')
    (U T : Submodule ℂ (Fin d → ℂ)) (hnd : n < d) (hT : IsRat T) (htd : Module.finrank ℂ ↥T < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ), IsRat S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ n * Module.finrank ℂ ↥S)
    (Z : Submodule ℚ (Fin d → ℂ)) [FiniteDimensional ℚ ↥Z] (hZU : ∀ x ∈ Z, x ∈ U)
    (hZL : ∀ x ∈ Z, ∀ i, x i ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) :
    (d - n) * Module.finrank ℚ ↥(Z ⊓ T.restrictScalars ℚ) ≤ d * Module.finrank ℂ ↥(U ⊓ T) := by
  obtain ⟨g, gM, gT⟩ := DiazModulus.roy_rat_adapted_basis T hT
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
  have : FiniteDimensional ℚ ↥(Z ⊓ T.restrictScalars ℚ) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let b := Module.finBasis ℚ ↥(Z ⊓ T.restrictScalars ℚ)
  have hbT : ∀ i, (b i : Fin d → ℂ) ∈ T := fun i => (Submodule.mem_inf.mp (b i).2).2
  have hbZ : ∀ i, (b i : Fin d → ℂ) ∈ Z := fun i => (Submodule.mem_inf.mp (b i).2).1
  have key := hIH _ htd (U.comap E) n d _ (fun i => P (b i)) hnd ?_ ?_ ?_ ?_
  · rwa [← hfin (U.comap E), hU'map] at key
  · intro S' hS'
    have hSrat : IsRat (S'.map E) := by
      apply le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
      calc S'.map E = (Submodule.span ℂ {v | v ∈ S' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)}).map E := by
            rw [hS']
        _ = Submodule.span ℂ (E '' {v | v ∈ S' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)}) := Submodule.map_span _ _
        _ ≤ _ := Submodule.span_mono (by
          rintro _ ⟨w, hw, rfl⟩
          refine ⟨Submodule.mem_map_of_mem hw.1, fun i => (isQ_iff _).mpr
            ((gM (Submodule.span ℚ {(1 : ℂ)}) (extZ d _ w) fun i => ?_).2 i)⟩
          rw [extZ_apply]; split_ifs
          · exact (isQ_iff _).mp (hw.2 _)
          · exact Submodule.zero_mem _)
    have h1 : (U.comap E ⊓ S').map E = U ⊓ S'.map E := by
      have hST : S'.map E ≤ T := by rintro _ ⟨w, -, rfl⟩; exact hET w
      rw [Submodule.map_inf E hEinj, hU'map, inf_assoc, inf_eq_right.mpr hST]
    rw [← hfin (U.comap E ⊓ S'), ← hfin S', h1]
    exact hss _ hSrat
  · intro i; show E (P (b i)) ∈ U; rw [hEP _ (hbT i)]; exact hZU _ (hbZ i)
  · intro i j; exact (gM _ _ (hZL _ (hbZ i))).1 (Fin.castLE htd' j)
  · apply LinearIndependent.of_comp (E.restrictScalars ℚ)
    have : (E.restrictScalars ℚ) ∘ (fun i => P (b i)) =
        (Z ⊓ T.restrictScalars ℚ).subtype ∘ b := funext fun i => hEP _ (hbT i)
    rw [this]
    exact b.linearIndependent.map' _ (Submodule.ker_subtype _)

end RC5_Q4

open DiazModulus RC5_Q4 in
theorem solution (hME : MultiplicityEstimateElem) {d : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ),
          Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
        LinearIndependent ℚ z' → (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥U')
    (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥U < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥U * Module.finrank ℂ ↥S)
    {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U)
    (hz : ∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) (hzind : LinearIndependent ℚ z) :
    (d - Module.finrank ℂ ↥U) * ℓ ≤ d * Module.finrank ℂ ↥U := by
  -- A1: lifts z_j = b_j + λ_j
  choose qf hqf using fun j i => (DiazModulus.ratLogAlg_mem_iff (z j i)).mp (hz j i)
  set η : Fin ℓ → (Fin d → ℂ) × (Fin d → ℂ) :=
    fun j => (fun i => ((qf j i : ℚ) : ℂ), fun i => z j i - qf j i) with hηdef
  have hη1 : ∀ j i, ∃ r : ℚ, (η j).1 i = (r : ℂ) := fun j i => ⟨qf j i, rfl⟩
  have hη2 : ∀ j i, (η j).2 i ∈ LogAlg := fun j i => hqf j i
  have hηz : ∀ j, (η j).1 + (η j).2 = z j := fun j => by funext i; simp [η]
  -- A2: the linear subgroup theorem at V = Υ⁻¹(U)
  have hdimV : Module.finrank ℂ ↥(U.comap (Ups d)) = Module.finrank ℂ ↥U + d := finrank_comap U
  have hspan := span_wfam d
  have hwK : ∀ k, wfam d k ∈ LinearMap.ker (Ups d) := fun k => hspan ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨V', q, φ, L₁, ℓT, hL₁, hℓT, hℓlt, hineq⟩ :=
    DiazModulus.linear_subgroup_transcendence hME (ι₀ := Fin d) (ι₁ := Fin d)
      (κ₀ := Fin d) (κ₁ := Fin ℓ) (U.comap (Ups d))
      (by rw [hdimV]; omega) (by simp only [hdimV, Fintype.card_fin]; omega)
      (by simp only [hdimV, Fintype.card_fin]; omega) (wfam d)
      (fun k => LinearMap.ker_le_comap _ (hwK k))
      (fun k => ⟨fun h => by simp only [wfam]; split_ifs; exacts [Qbar.neg_mem Qbar.one_mem, Qbar.zero_mem],
        fun i => by simp only [wfam]; split_ifs; exacts [Qbar.one_mem, Qbar.zero_mem]⟩)
      η (fun j => by rw [Submodule.mem_comap, Ups_apply, hηz]; exact hzU j)
      (fun j => ⟨fun h => SubfieldClass.ratCast_mem Qbar (qf j h), hη2 j⟩)
  -- A5: the relation rank
  have hρ := DiazModulus.roy_rat_relation_rank_le z hzind η hη1 hη2 hηz V' φ L₁ hL₁
  -- A3: d* − ℓ_T = d − dim(V' ⊔ L₁)
  simp only [Fintype.card_fin, hdimV] at hℓlt hineq
  rw [hspan] at hℓT
  have hWdim : Module.finrank ℂ ↥(LinearMap.ker (Ups d)) = d := by
    have h := finrank_ker_sup (d := d) ⊥
    rwa [sup_bot_eq, Submodule.map_bot, finrank_bot, add_zero] at h
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (Ups d)) (V'.prod L₁)
  have hX := finrank_prod' V' L₁
  have hWX := finrank_ker_sup (V'.prod L₁)
  rw [map_prod_ups] at hWX
  have hXd := Submodule.finrank_le (V' ⊔ L₁)
  have hV'd := Submodule.finrank_le V'
  have hL₁d := Submodule.finrank_le L₁
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hXd hV'd hL₁d
  have hδ : d - Module.finrank ℂ ↥V' + (d - Module.finrank ℂ ↥L₁) - ℓT =
      d - Module.finrank ℂ ↥(V' ⊔ L₁) := by omega
  have hdn : d + d - (Module.finrank ℂ ↥U + d) = d - Module.finrank ℂ ↥U := by omega
  rw [hδ, hdn] at hineq
  -- the rational space T = span(V' ∩ ℚ^d) ⊔ L₁
  set V₀ := Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, ∃ r : ℚ, v i = (r : ℂ)} with hV₀
  set T := V₀ ⊔ L₁ with hTdef
  have htX : Module.finrank ℂ ↥T ≤ Module.finrank ℂ ↥(V' ⊔ L₁) :=
    Submodule.finrank_mono (sup_le_sup_right (Submodule.span_le.mpr fun _ hv => hv.1) _)
  have htd : Module.finrank ℂ ↥T < d := by omega
  have hTrat : IsRat T := isRat_sup (isRat_span V') (L1_rat φ L₁ hL₁)
  have hl₁t : Module.finrank ℂ ↥L₁ ≤ Module.finrank ℂ ↥T := Submodule.finrank_mono le_sup_right
  have hineq' := hineq.trans (Nat.mul_le_mul_left d (Nat.sub_le_sub_left htX d))
  -- A6: the period space R
  set Z := Submodule.span ℚ (Set.range z) with hZdef
  have hZfin : FiniteDimensional ℚ ↥Z := FiniteDimensional.span_of_finite _ (Set.finite_range z)
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hcdef
  set F := Z ⊓ Submodule.span ℚ
    {x : Fin d → ℂ | ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧ x = τ + c • κ} with hFdef
  have hFfin : FiniteDimensional ℚ ↥F := Submodule.finiteDimensional_of_le inf_le_left
  have hZU : ∀ x ∈ Z, x ∈ U := fun x hx =>
    (Submodule.span_le (p := U.restrictScalars ℚ)).mpr (by rintro _ ⟨i, rfl⟩; exact hzU i) hx
  have hset : ∀ x ∈ Submodule.span ℚ
      {x : Fin d → ℂ | ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧ x = τ + c • κ},
      ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧ x = τ + c • κ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, T.zero_mem, 0, fun _ => ⟨0, by simp⟩, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨τ, hτ, κ, hκ, rfl⟩ := h1
      obtain ⟨τ', hτ', κ', hκ', rfl⟩ := h2
      refine ⟨τ + τ', T.add_mem hτ hτ', κ + κ', fun i => ?_, by rw [smul_add]; abel⟩
      obtain ⟨r, hr⟩ := hκ i
      obtain ⟨r', hr'⟩ := hκ' i
      exact ⟨r + r', by simp [hr, hr']⟩
    | smul a y _ h =>
      obtain ⟨τ, hτ, κ, hκ, rfl⟩ := h
      refine ⟨a • τ, (T.restrictScalars ℚ).smul_mem a hτ, a • κ, fun i => ?_,
        by rw [smul_add, smul_comm]⟩
      obtain ⟨r, hr⟩ := hκ i
      exact ⟨a * r, by simp [hr, Rat.smul_def]⟩
  obtain ⟨hRrat, hFR, hUR⟩ := DiazModulus.roy_rat_period_space c Complex.two_pi_I_ne_zero T U hTrat F
    hFfin (fun x hx => hZU x (Submodule.mem_inf.mp hx).1) (fun x hx => hset x (Submodule.mem_inf.mp hx).2)
  have hssR := hss _ hRrat
  -- A7: induction inside T
  have hFTZ : Module.finrank ℚ ↥(F ⊓ T.restrictScalars ℚ) ≤
      Module.finrank ℚ ↥(Z ⊓ T.restrictScalars ℚ) :=
    have := Submodule.finiteDimensional_of_le (inf_le_left : Z ⊓ T.restrictScalars ℚ ≤ Z)
    Submodule.finrank_mono (inf_le_inf_right _ inf_le_left)
  have hIHT := transport hIH U T hUd hTrat htd (fun S hS => hss S hS) Z hZU
    (span_coord _ fun i j => hz i j)
  -- A8
  exact arith hineq' hUd htd.le (rank_le_card _) hl₁t hFR hρ hUR hssR
    ((Nat.mul_le_mul_left _ hFTZ).trans hIHT)
