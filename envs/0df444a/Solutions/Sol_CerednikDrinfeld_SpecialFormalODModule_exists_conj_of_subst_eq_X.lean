-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_conj_of_subst_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d489eff3-e614-52ce-a535-341529942c4c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mOSConj

section Peel

variable {R : Type*} [CommRing R] {σ : Type*}

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem mem_span_X_of_constantCoeff [Fintype σ] [DecidableEq σ] {f : MvPowerSeries σ R}
    (hf : f.constantCoeff = 0) : f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul Finset.univ f (fun d hd => by
    have : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [this, coeff_zero_eq_constantCoeff_apply, hf])
  rw [hq]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem subst_mem_span [Fintype σ] [DecidableEq σ] {τ : Type*}
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, (a s).constantCoeff = 0)
    (f : MvPowerSeries σ R) (hf : f.constantCoeff = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  classical
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul Finset.univ f (fun d hd => by
    have : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [this, coeff_zero_eq_constantCoeff_apply, hf])
  rw [hq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, substAlgHom_X]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem span_X_eq_ker [Fintype σ] [DecidableEq σ] :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    exact constantCoeff_X s
  · intro f hf
    exact mem_span_X_of_constantCoeff hf

end Peel

section Kit

variable {k : Type u} [CommRing k]

abbrev Ser (k : Type u) [CommRing k] : Type u := Fin 2 → MvPowerSeries (Fin 2) k

abbrev inL (φ : Ser k) : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  fun i => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)

abbrev inR (φ : Ser k) : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  fun i => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)

theorem hasSubst_XL : HasSubst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
theorem hasSubst_XR : HasSubst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

variable {φ ψ : Ser k}

theorem constantCoeff_inL (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin 2) : (inL φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (hφ i)
theorem constantCoeff_inR (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin 2) : (inR φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (hφ i)

theorem subst_subst_fam {σ' τ : Type*} {φ' : Fin 2 → MvPowerSeries σ' k} {A : σ' → MvPowerSeries τ k}
    (hA : HasSubst A) (hφ : ∀ i, (φ' i).constantCoeff = 0) (g : MvPowerSeries (Fin 2) k) :
    subst A (subst φ' g) = subst (fun m => subst A (φ' m)) g :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hφ) hA g

theorem subst_subst_pull {τ : Type*} {T : Fin 2 ⊕ Fin 2 → MvPowerSeries τ k} (hT : HasSubst T)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (f : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    subst T (subst (Sum.elim (inL φ) (inR φ)) f)
      = subst (Sum.elim (fun i => subst (fun m => T (Sum.inl m)) (φ i))
          fun i => subst (fun m => T (Sum.inr m)) (φ i)) f := by
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)) hT]
  congr 1
  funext s; rcases s with j | j
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XL hT]
    congr 1; funext m; exact subst_X hT _
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XR hT]
    congr 1; funext m; exact subst_X hT _

theorem inL_comp (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    (fun i => subst (inL φ) (ψ i)) = inL (fun i => subst φ (ψ i)) := by
  funext i
  show _ = subst _ (subst φ (ψ i))
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hφ) hasSubst_XL]

theorem inR_comp (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    (fun i => subst (inR φ) (ψ i)) = inR (fun i => subst φ (ψ i)) := by
  funext i
  show _ = subst _ (subst φ (ψ i))
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hφ) hasSubst_XR]

end Kit

section Law

variable {k : Type u} [CommRing k] (F : MvFormalGroup 2 k) (α β : Ser k)

def pullLaw : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  fun j => subst (Sum.elim (inL α) (inR α)) (F.toPowerSeries j)

def conjSeries : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  fun i => subst (pullLaw F α) (β i)

theorem constantCoeff_pullLaw (hα0 : ∀ i, (α i).constantCoeff = 0) (j : Fin 2) : (pullLaw F α j).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim (constantCoeff_inL hα0) (constantCoeff_inR hα0))
    (by rintro (m | m); exacts [constantCoeff_inL hα0 m, constantCoeff_inR hα0 m]) (F.constantCoeff_eq_zero j)

theorem constantCoeff_conjSeries (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0) (i : Fin 2) : (conjSeries F α β i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (constantCoeff_pullLaw F α hα0))
    (constantCoeff_pullLaw F α hα0) (hβ0 i)

theorem cancel (hα0 : ∀ i, (α i).constantCoeff = 0) (hβα : ∀ i, subst β (α i) = X i) {τ : Type*} {W : Fin 2 → MvPowerSeries τ k} (hW : ∀ j, (W j).constantCoeff = 0)
    (hβ0' : ∀ i, (β i).constantCoeff = 0) (m : Fin 2) :
    subst (fun j => subst W (β j)) (α m) = W m := by
  rw [← subst_subst_fam (hasSubst_of_constantCoeff_zero hW) hβ0' (α m), hβα m]
  exact subst_X (hasSubst_of_constantCoeff_zero hW) m

theorem eval_conj (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0) {τ : Type*} {A B : Fin 2 → MvPowerSeries τ k}
    (hA : ∀ j, (A j).constantCoeff = 0) (hB : ∀ j, (B j).constantCoeff = 0) (i : Fin 2) :
    subst (Sum.elim A B) (conjSeries F α β i) =
      subst (fun j => subst (Sum.elim (fun m => subst A (α m)) fun m => subst B (α m)) (F.toPowerSeries j))
        (β i) := by
  show subst (Sum.elim A B) (subst (pullLaw F α) (β i)) = _
  rw [subst_subst_fam (MvFormalGroup.hasSubst_elim hA hB) (constantCoeff_pullLaw F α hα0) (β i)]
  congr 1
  funext j
  show subst (Sum.elim A B) (subst (Sum.elim (inL α) (inR α)) (F.toPowerSeries j)) = _
  rw [subst_subst_pull (MvFormalGroup.hasSubst_elim hA hB) hα0]
  rfl

theorem coeff_single_inL {φ : Ser k} (m j : Fin 2) :
    coeff (Finsupp.single (Sum.inl j) 1) (inL φ m) = coeff (Finsupp.single j 1) (φ m) ∧
    coeff (Finsupp.single (Sum.inr j) 1) (inL φ m) = 0 := by
  classical
  constructor
  · show coeff _ (subst _ (φ m)) = _
    rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _) (φ m) (Sum.inl j)]
    simp only [coeff_index_single_X, Sum.inl.injEq]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
    · intro t _ ht; rw [if_neg (Ne.symm ht), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · show coeff _ (subst _ (φ m)) = _
    rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _) (φ m) (Sum.inr j)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [coeff_index_single_X, if_neg Sum.inr_ne_inl, mul_zero]

theorem coeff_single_inR {φ : Ser k} (m j : Fin 2) :
    coeff (Finsupp.single (Sum.inr j) 1) (inR φ m) = coeff (Finsupp.single j 1) (φ m) ∧
    coeff (Finsupp.single (Sum.inl j) 1) (inR φ m) = 0 := by
  classical
  constructor
  · show coeff _ (subst _ (φ m)) = _
    rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _) (φ m) (Sum.inr j)]
    simp only [coeff_index_single_X, Sum.inr.injEq]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
    · intro t _ ht; rw [if_neg (Ne.symm ht), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · show coeff _ (subst _ (φ m)) = _
    rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _) (φ m) (Sum.inl j)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [coeff_index_single_X, if_neg Sum.inl_ne_inr, mul_zero]

theorem coeff_single_pullLaw (hα0 : ∀ i, (α i).constantCoeff = 0) (s j : Fin 2) :
    coeff (Finsupp.single (Sum.inl j) 1) (pullLaw F α s) = coeff (Finsupp.single j 1) (α s) ∧
    coeff (Finsupp.single (Sum.inr j) 1) (pullLaw F α s) = coeff (Finsupp.single j 1) (α s) := by
  classical
  have h0 : ∀ t, ((Sum.elim (inL α) (inR α)) t).constantCoeff = 0 := by
    rintro (m | m); exacts [constantCoeff_inL hα0 m, constantCoeff_inR hα0 m]
  constructor
  · show coeff _ (subst _ (F.toPowerSeries s)) = _
    rw [MvFormalGroup.coeff_single_subst h0 (F.toPowerSeries s) (Sum.inl j), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
      (coeff_single_inL _ _).1, (coeff_single_inR _ _).2, mul_zero, Finset.sum_const_zero, add_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · show coeff _ (subst _ (F.toPowerSeries s)) = _
    rw [MvFormalGroup.coeff_single_subst h0 (F.toPowerSeries s) (Sum.inr j), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
      (coeff_single_inL _ _).2, (coeff_single_inR _ _).1, mul_zero, Finset.sum_const_zero, zero_add,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lin_βα (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0) (hαβ : ∀ i, subst α (β i) = X i) (i j : Fin 2) :
    (∑ s, coeff (Finsupp.single s 1) (β i) * coeff (Finsupp.single j 1) (α s)) = if i = j then 1 else 0 := by
  classical
  rw [← MvFormalGroup.coeff_single_subst hα0 (β i) j, hαβ i, coeff_index_single_X]
  simp only [eq_comm]

def conjLaw (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0) (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : MvFormalGroup 2 k where
  toPowerSeries := conjSeries F α β
  constantCoeff_eq_zero := constantCoeff_conjSeries F α β hα0 hβ0
  coeff_single_inl i j := by
    classical
    show coeff _ (subst (pullLaw F α) (β i)) = _
    rw [MvFormalGroup.coeff_single_subst (constantCoeff_pullLaw F α hα0) (β i) (Sum.inl j)]
    simp only [(coeff_single_pullLaw F α hα0 _ _).1]
    exact lin_βα α β hα0 hβ0 hαβ i j
  coeff_single_inr i j := by
    classical
    show coeff _ (subst (pullLaw F α) (β i)) = _
    rw [MvFormalGroup.coeff_single_subst (constantCoeff_pullLaw F α hα0) (β i) (Sum.inr j)]
    simp only [(coeff_single_pullLaw F α hα0 _ _).2]
    exact lin_βα α β hα0 hβ0 hαβ i j
  assoc i := by

    have hX1 : ∀ l, ((fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) l).constantCoeff = 0 :=
      fun _ => constantCoeff_X _
    have hX2 : ∀ l, ((fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) l).constantCoeff = 0 :=
      fun _ => constantCoeff_X _
    have hX3 : ∀ l, ((fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) l).constantCoeff = 0 :=
      fun _ => constantCoeff_X _
    have hc0 := constantCoeff_conjSeries F α β hα0 hβ0

    have hαc : ∀ {A : Fin 2 → MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k} (hA : ∀ j, (A j).constantCoeff = 0) (m : Fin 2),
        (subst A (α m)).constantCoeff = 0 := fun hA m =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hA) hA (hα0 m)
    have hF12 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
        fun l => X (Sum.inr (Sum.inl l))) (conjSeries F α β j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hX1 hX2)
        (by rintro (l | l) <;> exact constantCoeff_X _) (hc0 j)
    have hF23 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
        fun l => X (Sum.inr (Sum.inr l))) (conjSeries F α β j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hX2 hX3)
        (by rintro (l | l) <;> exact constantCoeff_X _) (hc0 j)

    have hS : ∀ {a b : Fin 2 → MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k} (ha : ∀ j, (a j).constantCoeff = 0)
        (hb : ∀ j, (b j).constantCoeff = 0) (j : Fin 2),
        (subst (Sum.elim a b) (F.toPowerSeries j)).constantCoeff = 0 :=
      fun ha hb j => MvFormalGroup.constantCoeff_subst_elim F ha hb j
    rw [eval_conj F α β hα0 hβ0 hF12 hX3 i, eval_conj F α β hα0 hβ0 hX1 hF23 i]

    have hin12 : (fun m => subst (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
          fun l => X (Sum.inr (Sum.inl l))) (conjSeries F α β j)) (α m)) =
        fun m => subst (Sum.elim (fun m => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) (α m))
          fun m => subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) (α m)) (F.toPowerSeries m) := by
      funext m
      rw [show (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
          fun l => X (Sum.inr (Sum.inl l))) (conjSeries F α β j)) = fun j => subst _ (β j)
        from funext fun j => eval_conj F α β hα0 hβ0 hX1 hX2 j]
      exact cancel α β hα0 hβα (hS (hαc hX1) (hαc hX2)) hβ0 m
    have hin23 : (fun m => subst (fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
          fun l => X (Sum.inr (Sum.inr l))) (conjSeries F α β j)) (α m)) =
        fun m => subst (Sum.elim (fun m => subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) (α m))
          fun m => subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k)) (α m)) (F.toPowerSeries m) := by
      funext m
      rw [show (fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) k))
          fun l => X (Sum.inr (Sum.inr l))) (conjSeries F α β j)) = fun j => subst _ (β j)
        from funext fun j => eval_conj F α β hα0 hβ0 hX2 hX3 j]
      exact cancel α β hα0 hβα (hS (hαc hX2) (hαc hX3)) hβ0 m
    rw [hin12, hin23]
    congr 1
    funext j
    exact MvFormalGroup.subst_elim_assoc F (hαc hX1) (hαc hX2) (hαc hX3) j

theorem conjLaw_toPowerSeries (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0) (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : (conjLaw F α β hα0 hβ0 hαβ hβα).toPowerSeries = conjSeries F α β := by
  unfold conjLaw
  rfl

theorem isComm_conjLaw (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) [F.IsComm] :
    (conjLaw F α β hα0 hβ0 hαβ hβα).IsComm := by
  refine ⟨fun i => ?_⟩
  rw [conjLaw_toPowerSeries,
    eval_conj F α β hα0 hβ0 (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) i]
  have h : (fun j => subst (Sum.elim (fun m => subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m))
      fun m => subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m)) (F.toPowerSeries j)) = pullLaw F α := by
    funext j
    exact MvFormalGroup.subst_elim_comm F (a := inR α) (b := inL α) (constantCoeff_inR hα0) (constantCoeff_inL hα0) j
  rw [h]
  rfl

def conj (φ : Ser k) : Ser k := fun i => subst (fun m => subst α (φ m)) (β i)

theorem conj_apply (φ : Ser k) (i : Fin 2) : conj α β φ i = subst (fun m => subst α (φ m)) (β i) := rfl

theorem constantCoeff_comp {φ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (m : Fin 2) : (subst α (φ m)).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hα0) hα0 (hφ m)

theorem constantCoeff_conj {φ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin 2) : (conj α β φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (constantCoeff_comp α hα0 hφ))
    (constantCoeff_comp α hα0 hφ) (hβ0 i)

theorem comp_conj {φ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hβα : ∀ i, subst β (α i) = X i) (hφ : ∀ i, (φ i).constantCoeff = 0) (m : Fin 2) :
    subst (conj α β φ) (α m) = subst α (φ m) :=
  cancel α β hα0 hβα (constantCoeff_comp α hα0 hφ) hβ0 m

theorem conj_comp {φ ψ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hβα : ∀ i, subst β (α i) = X i)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) (i : Fin 2) :
    conj α β (fun j => subst φ (ψ j)) i = subst (conj α β φ) (conj α β ψ i) := by
  rw [conj_apply, conj_apply, subst_subst_fam (hasSubst_of_constantCoeff_zero (constantCoeff_conj α β hα0 hβ0 hφ))
    (constantCoeff_comp α hα0 hψ) (β i)]
  congr 1
  funext m
  rw [subst_subst_fam (hasSubst_of_constantCoeff_zero hα0) hφ (ψ m),
    subst_subst_fam (hasSubst_of_constantCoeff_zero (constantCoeff_conj α β hα0 hβ0 hφ)) hα0 (ψ m)]
  congr 1
  funext l
  exact (comp_conj α β hα0 hβ0 hβα hφ l).symm

theorem conj_X (hα0 : ∀ i, (α i).constantCoeff = 0) (hαβ : ∀ i, subst α (β i) = X i) (i : Fin 2) :
    conj α β (fun j => (X j : MvPowerSeries (Fin 2) k)) i = X i := by
  rw [conj_apply]
  have : (fun m => subst α (X m : MvPowerSeries (Fin 2) k)) = α :=
    funext fun m => subst_X (hasSubst_of_constantCoeff_zero hα0) m
  rw [this, hαβ i]

theorem subst_conjSeries_α (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hβα : ∀ i, subst β (α i) = X i) (l : Fin 2) :
    subst (conjSeries F α β) (α l) = pullLaw F α l := by
  show subst (fun i => subst (pullLaw F α) (β i)) (α l) = pullLaw F α l
  exact cancel α β hα0 hβα (constantCoeff_pullLaw F α hα0) hβ0 l

theorem isHom_conj {φ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i)
    (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) (i : Fin 2) :
    subst (conjSeries F α β) (conj α β φ i) =
      subst (Sum.elim (inL (conj α β φ)) (inR (conj α β φ))) (conjSeries F α β i) := by
  have hc0 := constantCoeff_conjSeries F α β hα0 hβ0
  have hcj0 := constantCoeff_conj α β hα0 hβ0 hφ
  have hPB : HasSubst (Sum.elim (inL α) (inR α)) :=
    MvFormalGroup.hasSubst_elim (constantCoeff_inL hα0) (constantCoeff_inR hα0)

  rw [eval_conj F α β hα0 hβ0 (constantCoeff_inL hcj0) (constantCoeff_inR hcj0) i]
  have hL : (fun m => subst (inL (conj α β φ)) (α m)) = inL (fun m => subst α (φ m)) := by
    rw [inL_comp hcj0 hα0]
    exact congrArg inL (funext fun m => comp_conj α β hα0 hβ0 hβα hφ m)
  have hR : (fun m => subst (inR (conj α β φ)) (α m)) = inR (fun m => subst α (φ m)) := by
    rw [inR_comp hcj0 hα0]
    exact congrArg inR (funext fun m => comp_conj α β hα0 hβ0 hβα hφ m)
  rw [hL, hR]

  rw [conj_apply, subst_subst_fam (hasSubst_of_constantCoeff_zero hc0) (constantCoeff_comp α hα0 hφ) (β i)]
  congr 1
  funext m
  rw [subst_subst_fam (hasSubst_of_constantCoeff_zero hc0) hα0 (φ m)]
  rw [show (fun l => subst (conjSeries F α β) (α l)) = pullLaw F α from
    funext fun l => subst_conjSeries_α F α β hα0 hβ0 hβα l]
  show subst (fun j => subst (Sum.elim (inL α) (inR α)) (F.toPowerSeries j)) (φ m) = _
  rw [← subst_subst_fam hPB F.constantCoeff_eq_zero (φ m), hφF m, subst_subst_pull hPB hφ]
  congr 1
  funext s
  rcases s with j | j
  · show subst (inL α) (φ j) = inL (fun m => subst α (φ m)) j
    exact congrFun (inL_comp hα0 hφ) j
  · show subst (inR α) (φ j) = inR (fun m => subst α (φ m)) j
    exact congrFun (inR_comp hα0 hφ) j

theorem conj_addVia {φ ψ : Ser k} (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hβα : ∀ i, subst β (α i) = X i)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) (i : Fin 2) :
    conj α β (fun j => subst (Sum.elim φ ψ) (F.toPowerSeries j)) i =
      subst (Sum.elim (conj α β φ) (conj α β ψ)) (conjSeries F α β i) := by
  rw [eval_conj F α β hα0 hβ0 (constantCoeff_conj α β hα0 hβ0 hφ) (constantCoeff_conj α β hα0 hβ0 hψ) i,
    conj_apply]
  congr 1
  funext j
  rw [MvFormalGroup.subst_subst_elim F hφ hψ (hasSubst_of_constantCoeff_zero hα0) j]
  congr 1
  funext s
  rcases s with m | m
  · exact (comp_conj α β hα0 hβ0 hβα hφ m).symm
  · exact (comp_conj α β hα0 hβ0 hβα hψ m).symm

end Law

section OD

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]

def conjOD (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : FormalODModule q k where
  F := conjLaw X₀.F α β hα0 hβ0 hαβ hβα
  isComm := by
    haveI := X₀.isComm
    exact isComm_conjLaw X₀.F α β hα0 hβ0 hαβ hβα
  act a := conj α β (X₀.act a)
  varpi := conj α β X₀.varpi
  isLawHom_act a := by
    refine ⟨constantCoeff_conj α β hα0 hβ0 (X₀.isLawHom_act a).1, fun i => ?_⟩
    rw [conjLaw_toPowerSeries]
    exact isHom_conj X₀.F α β hα0 hβ0 hαβ hβα (X₀.isLawHom_act a).1 (X₀.isLawHom_act a).2 i
  isLawHom_varpi := by
    refine ⟨constantCoeff_conj α β hα0 hβ0 X₀.isLawHom_varpi.1, fun i => ?_⟩
    rw [conjLaw_toPowerSeries]
    exact isHom_conj X₀.F α β hα0 hβ0 hαβ hβα X₀.isLawHom_varpi.1 X₀.isLawHom_varpi.2 i
  act_one := by
    rw [X₀.act_one]
    funext i
    exact conj_X α β hα0 hαβ i
  act_mul a b := by
    rw [X₀.act_mul]
    funext i
    exact conj_comp α β hα0 hβ0 hβα (X₀.isLawHom_act b).1 (X₀.isLawHom_act a).1 i
  act_add a b := by
    rw [X₀.act_add]
    funext i
    rw [show Series.addVia X₀.F (X₀.act a) (X₀.act b) =
      fun j => subst (Sum.elim (X₀.act a) (X₀.act b)) (X₀.F.toPowerSeries j) from rfl,
      show Series.addVia (conjLaw X₀.F α β hα0 hβ0 hαβ hβα) (conj α β (X₀.act a)) (conj α β (X₀.act b)) i =
        subst (Sum.elim (conj α β (X₀.act a)) (conj α β (X₀.act b)))
          ((conjLaw X₀.F α β hα0 hβ0 hαβ hβα).toPowerSeries i) from rfl,
      conjLaw_toPowerSeries]
    exact conj_addVia X₀.F α β hα0 hβ0 hβα (X₀.isLawHom_act a).1 (X₀.isLawHom_act b).1 i
  varpi_comp_varpi := by
    rw [← X₀.varpi_comp_varpi]
    funext i
    exact (conj_comp α β hα0 hβ0 hβα X₀.isLawHom_varpi.1 X₀.isLawHom_varpi.1 i).symm
  varpi_comp_act a := by
    show (fun i => subst (conj α β (X₀.act a)) (conj α β X₀.varpi i)) =
      fun i => subst (conj α β X₀.varpi) (conj α β (X₀.act (WittVector.frobenius a)) i)
    funext i
    rw [← conj_comp α β hα0 hβ0 hβα (X₀.isLawHom_act a).1 X₀.isLawHom_varpi.1 i,
      ← conj_comp α β hα0 hβ0 hβα X₀.isLawHom_varpi.1 (X₀.isLawHom_act _).1 i]
    exact congrFun (congrArg (conj α β) (X₀.varpi_comp_act a)) i

theorem conjOD_F (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : (conjOD X₀ α β hα0 hβ0 hαβ hβα).F = conjLaw X₀.F α β hα0 hβ0 hαβ hβα := by
  unfold conjOD
  rfl

theorem conjOD_act (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : (conjOD X₀ α β hα0 hβ0 hαβ hβα).act = fun a => conj α β (X₀.act a) := by
  unfold conjOD
  rfl

theorem conjOD_varpi (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : (conjOD X₀ α β hα0 hβ0 hαβ hβα).varpi = conj α β X₀.varpi := by
  unfold conjOD
  rfl

theorem linearPart_conj (α β : Ser k) (hα0 : ∀ i, (α i).constantCoeff = 0) {φ : Ser k} (hφ : ∀ i, (φ i).constantCoeff = 0) :
    MvFormalGroup.linearPart (conj α β φ) =
      MvFormalGroup.linearPart β * (MvFormalGroup.linearPart φ * MvFormalGroup.linearPart α) := by
  rw [show conj α β φ = fun i => subst (fun m => subst α (φ m)) (β i) from rfl,
    MvFormalGroup.linearPart_subst (constantCoeff_comp α hα0 hφ) β,
    MvFormalGroup.linearPart_subst hα0 φ]

theorem lin_mul_βα (α β : Ser k) (hα0 : ∀ i, (α i).constantCoeff = 0) (hαβ : ∀ i, subst α (β i) = X i) : MvFormalGroup.linearPart β * MvFormalGroup.linearPart α = 1 := by
  rw [← MvFormalGroup.linearPart_subst hα0 β,
    show (fun i => subst α (β i)) = fun i => (X i : MvPowerSeries (Fin 2) k) from funext hαβ,
    MvFormalGroup.linearPart_X]

theorem lin_mul_αβ (α β : Ser k) (hβ0 : ∀ i, (β i).constantCoeff = 0) (hβα : ∀ i, subst β (α i) = X i) : MvFormalGroup.linearPart α * MvFormalGroup.linearPart β = 1 := by
  rw [← MvFormalGroup.linearPart_subst hβ0 α,
    show (fun i => subst β (α i)) = fun i => (X i : MvPowerSeries (Fin 2) k) from funext hβα,
    MvFormalGroup.linearPart_X]

def lieEquiv (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (MvFormalGroup.linearPart β))
    (Matrix.mulVecLin (MvFormalGroup.linearPart α))
    (by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply, Matrix.mulVec_mulVec,
        lin_mul_βα α β hα0 hαβ, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply, Matrix.mulVec_mulVec,
        lin_mul_αβ α β hβ0 hβα, Matrix.one_mulVec])

theorem lieEquiv_symm_apply (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (m : Fin 2 → k) :
    (lieEquiv α β hα0 hβ0 hαβ hβα).symm m = Matrix.mulVec (MvFormalGroup.linearPart α) m := rfl

theorem lie_conj (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (c : Zp2 q → k) :
    (⨅ a, LinearMap.ker ((conjOD X₀ α β hα0 hβ0 hαβ hβα).lieAct a - c a • LinearMap.id) :
      Submodule k (Fin 2 → k)) =
    (⨅ a, LinearMap.ker (X₀.lieAct a - c a • LinearMap.id)).map
      (lieEquiv α β hα0 hβ0 hαβ hβα : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) := by
  ext m
  rw [Submodule.mem_map_equiv]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply, conjOD_act,
    lieEquiv_symm_apply]
  have hP := lin_mul_βα α β hα0 hαβ
  have hQ := lin_mul_αβ α β hβ0 hβα
  constructor
  · intro h a
    have h1 := congrArg (Matrix.mulVec (MvFormalGroup.linearPart α)) (h a)
    rw [linearPart_conj α β hα0 (X₀.isLawHom_act a).1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQ, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
    exact h1
  · intro h a
    rw [linearPart_conj α β hα0 (X₀.isLawHom_act a).1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h a,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

theorem lieZero_conj (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (j : Zp2 q →+* k) :
    (conjOD X₀ α β hα0 hβ0 hαβ hβα).lieZero j =
      (X₀.lieZero j).map (lieEquiv α β hα0 hβ0 hαβ hβα : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :=
  lie_conj X₀ α β hα0 hβ0 hαβ hβα (fun a => j a)

theorem lieOne_conj (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (j : Zp2 q →+* k) :
    (conjOD X₀ α β hα0 hβ0 hαβ hβα).lieOne j =
      (X₀.lieOne j).map (lieEquiv α β hα0 hβ0 hαβ hβα : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :=
  lie_conj X₀ α β hα0 hβ0 hαβ hβα (fun a => j (WittVector.frobenius a))

theorem isSpecial_conj (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (j : Zp2 q →+* k) (hX : X₀.IsSpecial j) :
    (conjOD X₀ α β hα0 hβ0 hαβ hβα).IsSpecial j := by
  obtain ⟨hc, h0, h1⟩ := hX
  set e := lieEquiv α β hα0 hβ0 hαβ hβα with he
  have hinj : Function.Injective (e : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) := e.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [lieZero_conj, lieOne_conj]
    refine isCompl_iff.mpr ⟨?_, ?_⟩
    · rw [disjoint_iff, ← Submodule.map_inf _ hinj, disjoint_iff.mp hc.disjoint, Submodule.map_bot]
    · rw [codisjoint_iff, ← Submodule.map_sup, codisjoint_iff.mp hc.codisjoint, Submodule.map_top,
        LinearEquiv.range]
  · rw [lieZero_conj]
    haveI := h0
    exact Module.Invertible.congr (Submodule.equivMapOfInjective _ hinj (X₀.lieZero j))
  · rw [lieOne_conj]
    haveI := h1
    exact Module.Invertible.congr (Submodule.equivMapOfInjective _ hinj (X₀.lieOne j))

theorem span_range_eq_span_X {B : Type u} [CommRing B] (α' β' : Fin 2 → MvPowerSeries (Fin 2) B)
    (hα0' : ∀ i, (α' i).constantCoeff = 0) (hβ0' : ∀ i, (β' i).constantCoeff = 0)
    (hαβ' : ∀ i, subst α' (β' i) = X i) :
    Ideal.span (Set.range α') = Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
  classical
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact mem_span_X_of_constantCoeff (hα0' i)
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [← hαβ' i]
    exact subst_mem_span α' hα0' (β' i) (hβ0' i)

theorem finrank_quotient_span_X (κ : Type u) [Field κ] :
    Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) κ))) ∧
    Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) κ))) = 1 := by
  classical
  let cc : MvPowerSeries (Fin 2) κ →ₐ[κ] κ :=
    { (constantCoeff : MvPowerSeries (Fin 2) κ →+* κ) with
      commutes' := fun r => by
        show constantCoeff (algebraMap κ (MvPowerSeries (Fin 2) κ) r) = r
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact constantCoeff_C (σ := Fin 2) r }
  have hsurj : Function.Surjective cc := fun r => ⟨C r, constantCoeff_C (σ := Fin 2) r⟩
  have hker : RingHom.ker cc.toRingHom = Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) κ)) := by
    rw [span_X_eq_ker]
  let e : (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) κ))) ≃ₐ[κ] κ :=
    (Ideal.quotientEquivAlgOfEq κ hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨Module.Finite.equiv e.symm.toLinearEquiv, ?_⟩
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]

theorem hasKernelOfDegree_one (α β : Ser k) (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) : FormalODModule.HasKernelOfDegree α 1 := by
  have hsp := span_range_eq_span_X α β hα0 hβ0 hαβ
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · show Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range α))
    rw [hsp]
    exact (finrank_quotient_span_X k).1
  · show Module.Projective k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range α))
    rw [hsp]
    haveI := (finrank_quotient_span_X k).1
    infer_instance
  · show Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (Series.map f α))) = 1
    have hα0' : ∀ i, (Series.map f α i).constantCoeff = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map f (α i)) = 0
      rw [constantCoeff_map, hα0 i, map_zero]
    have hβ0' : ∀ i, (Series.map f β i).constantCoeff = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map f (β i)) = 0
      rw [constantCoeff_map, hβ0 i, map_zero]
    have hαβ' : ∀ i, subst (Series.map f α) (Series.map f β i) = X i := fun i => by
      show subst (fun m => MvPowerSeries.map f (α m)) (MvPowerSeries.map f (β i)) = X i
      rw [← map_subst (hasSubst_of_constantCoeff_zero hα0), hαβ i, map_X]
    rw [span_range_eq_span_X (Series.map f α) (Series.map f β) hα0' hβ0' hαβ']
    exact (finrank_quotient_span_X κ).2

theorem map_id_series (φ : Ser k) : Series.map (RingHom.id k) φ = φ := by
  funext i
  show MvPowerSeries.map (RingHom.id k) (φ i) = φ i
  rw [MvPowerSeries.map_id]
  rfl

theorem hasHeight_conj (X₀ : FormalODModule q k) (α β : Ser k)
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (hβα : ∀ i, subst β (α i) = X i) (hX : X₀.HasHeight 4) : (conjOD X₀ α β hα0 hβ0 hαβ hβα).HasHeight 4 := by
  have hq0 : ∀ i, ((X₀.act (q : Zp2 q)).comp α i).constantCoeff = 0 :=
    fun i => constantCoeff_comp α hα0 (X₀.isLawHom_act _).1 i
  have h1 := FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id k) hX hα0
    (hasKernelOfDegree_one α β hα0 hβ0 hαβ)
  rw [map_id_series] at h1
  have h2 := FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id k)
    (hasKernelOfDegree_one β α hβ0 hα0 hβα) hq0 h1
  rw [map_id_series, one_mul, mul_one] at h2
  show FormalODModule.HasKernelOfDegree ((conjOD X₀ α β hα0 hβ0 hαβ hβα).act (q : Zp2 q)) (q ^ 4)
  rw [conjOD_act]
  exact h2

end OD

end P2mOSConj

end

universe u

open MvPowerSeries P2mOSConj CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (α β : Fin 2 → MvPowerSeries (Fin 2) k)
    (hα0 : ∀ i, MvPowerSeries.constantCoeff (α i) = 0) (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0)
    (hαβ : ∀ i, MvPowerSeries.subst α (β i) = MvPowerSeries.X i)
    (hβα : ∀ i, MvPowerSeries.subst β (α i) = MvPowerSeries.X i) :
    ∃ X₁ : SpecialFormalODModule q j₀,
      (∀ i, X₁.F.toPowerSeries i =
        MvPowerSeries.subst
          (fun j => MvPowerSeries.subst
            (Sum.elim
              (fun m => MvPowerSeries.subst
                (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m))
              fun m => MvPowerSeries.subst
                (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m))
            (X₀.F.toPowerSeries j))
          (β i)) ∧
      (∀ a, X₁.act a = Series.comp β (Series.comp (X₀.act a) α)) ∧
      X₁.varpi = Series.comp β (Series.comp X₀.varpi α) := by
  refine ⟨{ toFormalODModule := conjOD X₀.toFormalODModule α β hα0 hβ0 hαβ hβα,
            isSpecial := isSpecial_conj X₀.toFormalODModule α β hα0 hβ0 hαβ hβα j₀ X₀.isSpecial,
            hasHeight := hasHeight_conj X₀.toFormalODModule α β hα0 hβ0 hαβ hβα X₀.hasHeight }, ?_, ?_, ?_⟩
  · intro i
    show (conjOD X₀.toFormalODModule α β hα0 hβ0 hαβ hβα).F.toPowerSeries i = _
    rw [conjOD_F, conjLaw_toPowerSeries]
    rfl
  · intro a
    show (conjOD X₀.toFormalODModule α β hα0 hβ0 hαβ hβα).act a = _
    rw [conjOD_act]
    rfl
  · show (conjOD X₀.toFormalODModule α β hα0 hβ0 hαβ hβα).varpi = _
    rw [conjOD_varpi]
    rfl

end S_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X (solution)
