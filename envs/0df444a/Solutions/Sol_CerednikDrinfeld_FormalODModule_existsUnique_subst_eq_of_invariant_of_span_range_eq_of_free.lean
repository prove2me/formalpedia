-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a034a0ed-c4af-532b-83ea-27ad849da269

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top
import Theorems.Thm_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace QAClosing

open MvPowerSeries

section Generic

variable {R : Type} [CommRing R] {σ : Type}

theorem X_mem_jacobson_bot (s : σ) :
    (X s : MvPowerSeries σ R) ∈ Ideal.jacobson (⊥ : Ideal (MvPowerSeries σ R)) := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  rw [isUnit_iff_constantCoeff]
  simp

theorem span_X_le_jacobson :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.span_le]
  rintro _ ⟨s, rfl⟩
  exact X_mem_jacobson_bot s

theorem mem_span_X_pow_of_forall_coeff [DecidableEq σ] (q : ℕ) (S : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ m : σ →₀ ℕ, coeff m f ≠ 0 → ∃ s ∈ S, q ≤ m s) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ q) '' (S : Set σ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext m
      by_contra h
      obtain ⟨s, hs, -⟩ := hf m h
      simp at hs
    simp [this]
  | insert a S' ha IH =>
    intro f hf
    let f₁ : MvPowerSeries σ R := fun m => if q ≤ m a then f m else 0
    let f₂ : MvPowerSeries σ R := fun m => if q ≤ m a then 0 else f m
    have hsplit : f = f₁ + f₂ := by
      ext m
      show coeff m f = coeff m f₁ + coeff m f₂
      simp only [f₁, f₂, coeff_apply]
      split_ifs <;> simp
    have h1 : (X a : MvPowerSeries σ R) ^ q ∣ f₁ := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp only [f₁, coeff_apply]
      rw [if_neg (not_le.2 hm)]
    have h2 : f₂ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ q) '' (S' : Set σ)) := by
      apply IH
      intro m hm
      have hm' : coeff m f ≠ 0 ∧ ¬ q ≤ m a := by
        simp only [f₂, coeff_apply] at hm
        by_cases h : q ≤ m a
        · rw [if_pos h] at hm; exact (hm rfl).elim
        · rw [if_neg h] at hm; exact ⟨hm, h⟩
      obtain ⟨s, hs, hqs⟩ := hf m hm'.1
      rcases Finset.mem_insert.1 hs with rfl | hs'
      · exact (hm'.2 hqs).elim
      · exact ⟨s, hs', hqs⟩
    rw [hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · obtain ⟨g, hg⟩ := h1
      rw [hg]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_, rfl⟩)
      simp
    · refine Ideal.span_mono ?_ h2
      apply Set.image_mono
      intro s hs
      exact Finset.mem_insert_of_mem hs

theorem mem_span_X_of_constantCoeff_eq_zero [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  have := mem_span_X_pow_of_forall_coeff (R := R) 1 (Finset.univ : Finset σ) f ?_
  · simpa using this
  · intro m hm
    by_contra h
    push Not at h
    have : m = 0 := by
      ext s
      have := h s (Finset.mem_univ s)
      simpa using this
    subst this
    exact hm (by simpa using hf)

theorem sub_trunc'_mem_span_X_pow [Fintype σ] [DecidableEq σ] (q : ℕ) (f : MvPowerSeries σ R) :
    f - ((trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => q) f : MvPolynomial σ R) :
        MvPowerSeries σ R) ∈
      Ideal.span (Set.range fun s => (X s : MvPowerSeries σ R) ^ (q + 1)) := by
  have := mem_span_X_pow_of_forall_coeff (R := R) (q + 1) (Finset.univ : Finset σ)
    (f - ((trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => q) f : MvPolynomial σ R) :
        MvPowerSeries σ R)) ?_
  · simpa using this
  · intro m hm
    by_contra h
    push Not at h
    have hle : m ≤ Finsupp.equivFunOnFinite.symm (fun _ : σ => q) := by
      intro s
      have := h s (Finset.mem_univ s)
      show m s ≤ (Finsupp.equivFunOnFinite.symm fun _ : σ => q) s
      rw [Finsupp.coe_equivFunOnFinite_symm]
      omega
    apply hm
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]

theorem ringHom_ext_of_map_X_pow [Fintype σ] [DecidableEq σ] {T : Type} [Semiring T]
    (g h : MvPowerSeries σ R →+* T) (q : ℕ)
    (hg : ∀ s, g ((X s) ^ (q + 1)) = 0) (hh : ∀ s, h ((X s) ^ (q + 1)) = 0)
    (hC : ∀ r : R, g (C r) = h (C r)) (hX : ∀ s, g (X s) = h (X s)) : g = h := by
  have hpoly : g.comp (MvPolynomial.coeToMvPowerSeries.ringHom) =
      h.comp (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun s => ?_)
    · simpa using hC r
    · simpa using hX s
  have hker : ∀ (φ : MvPowerSeries σ R →+* T), (∀ s, φ ((X s) ^ (q + 1)) = 0) →
      ∀ d ∈ Ideal.span (Set.range fun s => (X s : MvPowerSeries σ R) ^ (q + 1)), φ d = 0 := by
    intro φ hφ d hd
    have : Ideal.span (Set.range fun s => (X s : MvPowerSeries σ R) ^ (q + 1)) ≤
        RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hφ s
    exact this hd
  ext f
  have hd := sub_trunc'_mem_span_X_pow (R := R) q f
  set P := trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => q) f
  have hf : f = (P : MvPowerSeries σ R) + (f - (P : MvPowerSeries σ R)) := by ring
  rw [hf, map_add, map_add, hker g hg _ hd, hker h hh _ hd]
  congr 1
  exact congrArg (fun ψ : MvPolynomial σ R →+* T => ψ P) hpoly

end Generic

noncomputable section Setup

variable {B : Type} [CommRing B]

abbrev A (B : Type) [CommRing B] : Type := MvPowerSeries (Fin 2) B

variable {C : Type} [CommRing C] [Algebra B C] (π : A B →ₐ[B] C) (I : Ideal (A B))

abbrev M (C : Type) [CommRing C] : Type := MvPowerSeries (Fin 2) C

def ybar (l : Fin 2) : C := π (X l)

def aψ : Fin 2 ⊕ Fin 2 → M C :=
  Sum.elim (fun l => X l) (fun l => MvPowerSeries.C (ybar π l))

structure Hyp : Prop where
  ker : ∀ a : A B, π a = 0 ↔ a ∈ I
  surj : Function.Surjective π
  nil : ∃ q : ℕ, ∀ i : Fin 2, (X i : A B) ^ q ∈ I

variable {π I}

theorem Hyp.nil_succ (H : Hyp π I) : ∃ q : ℕ, ∀ i : Fin 2, (X i : A B) ^ (q + 1) ∈ I := by
  obtain ⟨q, hq⟩ := H.nil
  exact ⟨q, fun i => by rw [pow_succ]; exact Ideal.mul_mem_right _ _ (hq i)⟩

theorem Hyp.map_X_pow (H : Hyp π I) : ∃ q : ℕ, ∀ i : Fin 2, π ((X i : A B) ^ (q + 1)) = 0 := by
  obtain ⟨q, hq⟩ := H.nil_succ
  exact ⟨q, fun i => (H.ker _).2 (hq i)⟩

theorem isNilpotent_ybar (H : Hyp π I) (l : Fin 2) : IsNilpotent (ybar π l) := by
  obtain ⟨q, hq⟩ := H.map_X_pow
  exact ⟨q + 1, by rw [ybar, ← map_pow]; exact hq l⟩

theorem hasSubst_aψ (H : Hyp π I) : HasSubst (aψ π) := by
  apply hasSubst_of_constantCoeff_nilpotent
  rintro (l | l)
  · simp [aψ]
  · simpa [aψ] using isNilpotent_ybar H l

theorem hasSubst_X_inl :
    HasSubst (fun l : Fin 2 => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_X_inr :
    HasSubst (fun l : Fin 2 => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_elim_zero_X :
    HasSubst (Sum.elim (fun _ : Fin 2 => (0 : A B)) (fun l : Fin 2 => (X l : A B))) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (l | l) <;> simp

theorem hasSubst_X' : HasSubst (fun l : Fin 2 => (X l : A B)) :=
  hasSubst_of_constantCoeff_zero fun l => constantCoeff_X l

theorem subst_X_eq_algebraMap (a : A B) :
    subst (fun l : Fin 2 => (X l : M C)) a = algebraMap (A B) (M C) a := by
  rw [← map_algebraMap_eq_subst_X]
  rfl

theorem ψ_subst_inl (H : Hyp π I) (a : A B) :
    subst (aψ π) (subst (fun l : Fin 2 => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) a) =
      algebraMap (A B) (M C) a := by
  rw [subst_comp_subst_apply hasSubst_X_inl (hasSubst_aψ H)]
  have : (fun l : Fin 2 => subst (aψ π)
      ((fun l : Fin 2 => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) l)) =
      fun l : Fin 2 => (X l : M C) := by
    funext l
    rw [subst_X (hasSubst_aψ H)]
    rfl
  rw [this, subst_X_eq_algebraMap]

theorem subst_C_ybar (H : Hyp π I) (c : A B) :
    subst (fun l : Fin 2 => (MvPowerSeries.C (ybar π l) : M C)) c = MvPowerSeries.C (π c) := by
  classical
  obtain ⟨q, hq⟩ := H.map_X_pow
  have hb : HasSubst (fun l : Fin 2 => (MvPowerSeries.C (ybar π l) : M C)) :=
    hasSubst_of_constantCoeff_nilpotent fun l => by simpa using isNilpotent_ybar H l
  have key := ringHom_ext_of_map_X_pow (R := B) (σ := Fin 2)
    ((substAlgHom hb).toRingHom) ((MvPowerSeries.C : C →+* M C).comp π.toRingHom) q
    ?_ ?_ ?_ ?_
  · have := congrArg (fun φ : A B →+* M C => φ c) key
    simpa [substAlgHom_apply] using this
  · intro s
    rw [map_pow]
    show (substAlgHom hb (X s)) ^ (q + 1) = 0
    rw [substAlgHom_X, ← map_pow, ybar, ← map_pow, hq s, map_zero]
  · intro s
    show MvPowerSeries.C (π ((X s) ^ (q + 1))) = 0
    rw [hq s, map_zero]
  · intro r
    show substAlgHom hb (algebraMap B (A B) r) = MvPowerSeries.C (π (algebraMap B (A B) r))
    rw [AlgHom.commutes, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
  · intro s
    show substAlgHom hb (X s) = MvPowerSeries.C (π (X s))
    rw [substAlgHom_X]
    rfl

theorem ψ_subst_inr (H : Hyp π I) (c : A B) :
    subst (aψ π) (subst (fun l : Fin 2 => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) c) =
      MvPowerSeries.C (π c) := by
  rw [subst_comp_subst_apply hasSubst_X_inr (hasSubst_aψ H)]
  have : (fun l : Fin 2 => subst (aψ π)
      ((fun l : Fin 2 => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) l)) =
      fun l : Fin 2 => (MvPowerSeries.C (ybar π l) : M C) := by
    funext l
    rw [subst_X (hasSubst_aψ H)]
    rfl
  rw [this, subst_C_ybar H]

theorem ψ_eq_zero_of_mem (H : Hyp π I)
    {f : MvPowerSeries (Fin 2 ⊕ Fin 2) B}
    (hf : f ∈ Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))) :
    subst (aψ π) f = 0 := by
  rw [← substAlgHom_apply (hasSubst_aψ H)]
  have : Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))) ≤
      RingHom.ker (substAlgHom (hasSubst_aψ H)).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show substAlgHom (hasSubst_aψ H) (subst _ c) = 0
    rw [substAlgHom_apply, ψ_subst_inr H, (H.ker c).2 hc, map_zero]
  exact this hf

theorem constantCoeff_ψ (H : Hyp π I) (f : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    constantCoeff (subst (aψ π) f) =
      π (subst (Sum.elim (fun _ : Fin 2 => (0 : A B)) (fun l => X l)) f) := by
  classical
  obtain ⟨q, hq⟩ := H.map_X_pow
  have key := ringHom_ext_of_map_X_pow (R := B) (σ := Fin 2 ⊕ Fin 2)
    ((constantCoeff : M C →+* C).comp (substAlgHom (hasSubst_aψ H)).toRingHom)
    (π.toRingHom.comp (substAlgHom (hasSubst_elim_zero_X (B := B))).toRingHom) q
    ?_ ?_ ?_ ?_
  · have := congrArg (fun φ : MvPowerSeries (Fin 2 ⊕ Fin 2) B →+* C => φ f) key
    simpa [substAlgHom_apply] using this
  · intro s
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_pow, substAlgHom_X]
    rcases s with l | l
    · simp only [aψ, Sum.elim_inl, constantCoeff_X]
      exact zero_pow (Nat.succ_ne_zero q)
    · simp only [aψ, Sum.elim_inr, constantCoeff_C]
      rw [ybar, ← map_pow, hq l]
  · intro s
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_pow, substAlgHom_X]
    rcases s with l | l
    · simp only [Sum.elim_inl, map_zero]
      exact zero_pow (Nat.succ_ne_zero q)
    · simp only [Sum.elim_inr]
      rw [← map_pow]
      exact hq l
  · intro r
    show constantCoeff (substAlgHom (hasSubst_aψ H) (algebraMap B _ r)) =
      π (substAlgHom (hasSubst_elim_zero_X (B := B)) (algebraMap B _ r))
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes,
      MvPowerSeries.algebraMap_apply, constantCoeff_C]
  · intro s
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      substAlgHom_X]
    rcases s with l | l
    · simp only [aψ, Sum.elim_inl, constantCoeff_X, map_zero]
    · simp only [aψ, Sum.elim_inr, constantCoeff_C, ybar]

theorem subst_map_algebraMap {a : Fin 2 → M C} (ha : HasSubst a) (c : A B) :
    subst a (MvPowerSeries.map (algebraMap B C) c) = subst a c := by
  rw [map_algebraMap_eq_subst_X, subst_comp_subst_apply hasSubst_X' ha]
  congr 1
  funext s
  exact subst_X ha s

end Setup

noncomputable section Torsor

variable {B : Type} [CommRing B] {C : Type} [CommRing C] [Algebra B C] {π : A B →ₐ[B] C}
  {I : Ideal (A B)} (H : Hyp π I) (F : MvFormalGroup 2 B)

include H

def δbar : A B →ₐ[B] M C :=
  (substAlgHom (hasSubst_aψ H)).comp (substAlgHom F.hasSubst_toPowerSeries)

theorem δbar_apply (w : A B) :
    δbar H F w = subst (aψ π) (subst F.toPowerSeries w) := by
  show substAlgHom (hasSubst_aψ H) (substAlgHom F.hasSubst_toPowerSeries w) = _
  rw [substAlgHom_apply, substAlgHom_apply]

theorem constantCoeff_Fbar (j : Fin 2) :
    constantCoeff (subst (aψ π) (F.toPowerSeries j)) = ybar π j := by
  rw [constantCoeff_ψ H, MvFormalGroup.subst_elim_zero_left F (fun j => constantCoeff_X j) j]
  rfl

theorem hasSubst_Fbar : HasSubst (fun j : Fin 2 => subst (aψ π) (F.toPowerSeries j)) :=
  hasSubst_of_constantCoeff_nilpotent fun j => by
    rw [constantCoeff_Fbar H F]; exact isNilpotent_ybar H j

theorem δbar_eq_subst (w : A B) :
    δbar H F w = subst (fun j : Fin 2 => subst (aψ π) (F.toPowerSeries j)) w := by
  rw [δbar_apply, subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_aψ H)]

theorem constantCoeff_δbar (w : A B) :
    constantCoeff (δbar H F w) = π w := by
  rw [δbar_apply, constantCoeff_ψ H,
    subst_comp_subst_apply F.hasSubst_toPowerSeries hasSubst_elim_zero_X]
  have : (fun j : Fin 2 => subst (Sum.elim (fun _ : Fin 2 => (0 : A B)) (fun l => X l))
      (F.toPowerSeries j)) = fun j => (X j : A B) :=
    funext fun j => MvFormalGroup.subst_elim_zero_left F (fun j => constantCoeff_X j) j
  rw [this]
  congr 1
  exact congrFun subst_self w

theorem δbar_eq_algebraMap_of_invariant (w : A B)
    (hw : MvPowerSeries.subst F.toPowerSeries w -
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B)))) :
    δbar H F w = algebraMap (A B) (M C) w := by
  rw [δbar_apply, ← ψ_subst_inl H w, ← sub_eq_zero, ← subst_sub (hasSubst_aψ H)]
  exact ψ_eq_zero_of_mem H hw

theorem δbar_subst_eq_algebraMap (u : Fin 2 → A B) (hu0 : ∀ j, constantCoeff (u j) = 0)
    (huinv : ∀ j, δbar H F (u j) = algebraMap (A B) (M C) (u j)) (c : A B) :
    δbar H F (subst u c) = algebraMap (A B) (M C) (subst u c) := by
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  rw [δbar_eq_subst, subst_comp_subst_apply hu (hasSubst_Fbar H F)]
  have h1 : (fun j : Fin 2 => subst (fun j : Fin 2 => subst (aψ π) (F.toPowerSeries j)) (u j)) =
      fun j => algebraMap (A B) (M C) (u j) := by
    funext j
    rw [← δbar_eq_subst H, huinv]
  rw [h1]
  have halg : HasSubst (fun j : Fin 2 => algebraMap (A B) (M C) (u j)) := by
    apply hasSubst_of_constantCoeff_zero
    intro j
    show constantCoeff (MvPowerSeries.map (algebraMap B C) (u j)) = 0
    rw [constantCoeff_map, hu0, map_zero]
  show _ = MvPowerSeries.map (algebraMap B C) (subst u c)
  rw [map_subst hu]
  exact (subst_map_algebraMap halg c).symm

def N : Submodule (A B) (M C) := Submodule.span (A B) (Set.range (δbar H F))

theorem mul_mem_N {x y : M C} (hx : x ∈ N H F) (hy : y ∈ N H F) : x * y ∈ N H F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem one_mem_N : (1 : M C) ∈ N H F := by
  have : δbar H F 1 = 1 := map_one _
  exact this ▸ Submodule.subset_span ⟨1, rfl⟩

theorem algebraMap_mem_N (a : A B) : algebraMap (A B) (M C) a ∈ N H F := by
  have := Submodule.smul_mem (N H F) a (one_mem_N H F)
  rwa [Algebra.smul_def, mul_one] at this

theorem top_le_N_sup :
    (⊤ : Submodule (A B) (M C)) ≤
      N H F ⊔ Ideal.span (Set.range (X : Fin 2 → A B)) • (⊤ : Submodule (A B) (M C)) := by
  classical
  intro f _
  obtain ⟨a, ha⟩ := H.surj (constantCoeff f)
  have hn : δbar H F a ∈ N H F := Submodule.subset_span ⟨a, rfl⟩
  have h0 : constantCoeff (f - δbar H F a) = 0 := by
    rw [map_sub, constantCoeff_δbar, ha, sub_self]
  have hmem : f - δbar H F a ∈
      Ideal.span (Set.range (X : Fin 2 → A B)) • (⊤ : Submodule (A B) (M C)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_span]
    have h := mem_span_X_of_constantCoeff_eq_zero (f - δbar H F a) h0
    refine Ideal.span_mono ?_ h
    rintro _ ⟨s, rfl⟩
    refine ⟨X s, ⟨s, rfl⟩, ?_⟩
    show MvPowerSeries.map (algebraMap B C) (X s) = X s
    exact map_X _ s
  have hf : f = δbar H F a + (f - δbar H F a) := by abel
  rw [hf]
  exact Submodule.add_mem_sup hn hmem

theorem N_eq_top [Module.Finite (A B) (M C)] : N H F = ⊤ := by
  refine top_le_iff.mp ?_
  exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top span_X_le_jacobson
    (top_le_N_sup H F)

end Torsor

noncomputable section Rank

variable {B : Type} [CommRing B] {C : Type} [CommRing C] [Algebra B C] {π : A B →ₐ[B] C}
  {I : Ideal (A B)} (H : Hyp π I) (F : MvFormalGroup 2 B)
variable {ι : Type} [Fintype ι] [DecidableEq ι] (bC : Module.Basis ι B C)

def Ψ : (ι → A B) →ₗ[A B] M C :=
  (Pi.basisFun (A B) ι).constr (A B) fun k => (MvPowerSeries.C (bC k) : M C)

theorem Ψ_apply (a : ι → A B) : Ψ bC a = ∑ k, a k • (MvPowerSeries.C (bC k) : M C) := by
  simp [Ψ, Module.Basis.constr_apply_fintype]

theorem coeff_Ψ (a : ι → A B) (e : Fin 2 →₀ ℕ) :
    coeff e (Ψ bC a) = ∑ k, coeff e (a k) • bC k := by
  rw [Ψ_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, coeff_mul_C, Algebra.smul_def]
  congr 1

theorem Ψ_bijective : Function.Bijective (Ψ (B := B) bC) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    funext k
    ext e
    have h := congrArg (coeff e) ha
    rw [coeff_Ψ, map_zero] at h
    have := Fintype.linearIndependent_iff.1 bC.linearIndependent (fun k => coeff e (a k)) h k
    simpa using this
  · intro f
    refine ⟨fun k => fun e => bC.repr (coeff e f) k, ?_⟩
    ext e
    rw [coeff_Ψ]
    conv_rhs => rw [← bC.sum_repr (coeff e f)]
    rfl

def eM : (ι → A B) ≃ₗ[A B] M C := LinearEquiv.ofBijective (Ψ bC) (Ψ_bijective bC)

include bC in
theorem finite_M : Module.Finite (A B) (M C) := Module.Finite.equiv (eM bC)

include H

variable (b : ι → A B)
variable (u : Fin 2 → A B) (hu0 : ∀ j, constantCoeff (u j) = 0)
  (huinv : ∀ j, δbar H F (u j) = algebraMap (A B) (M C) (u j))
  (hΦ : ∀ f : A B, ∃ c : ι → A B, f = ∑ k, subst u (c k) * b k)

def φ : (ι → A B) →ₗ[A B] M C :=
  (Pi.basisFun (A B) ι).constr (A B) fun k => δbar H F (b k)

theorem φ_apply (a : ι → A B) : φ H F b a = ∑ k, a k • δbar H F (b k) := by
  simp [φ, Module.Basis.constr_apply_fintype]

include hu0 huinv in
theorem φ_subst (c : ι → A B) :
    φ H F b (fun k => subst u (c k)) = δbar H F (∑ k, subst u (c k) * b k) := by
  rw [φ_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, δbar_subst_eq_algebraMap H F u hu0 huinv, Algebra.smul_def]

include hu0 huinv hΦ in
theorem φ_surjective [Module.Finite (A B) (M C)] : Function.Surjective (φ H F b) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← N_eq_top H F, N, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := hΦ a
  exact ⟨fun k => subst u (c k), by rw [φ_subst H F b u hu0 huinv, ← hc]⟩

include bC hu0 huinv hΦ in
theorem φ_injective : Function.Injective (φ H F b) := by
  haveI : Module.Finite (A B) (M C) := finite_M bC
  let g : (ι → A B) →ₗ[A B] (ι → A B) := (eM bC).symm.toLinearMap.comp (φ H F b)
  have hg : Function.Surjective g :=
    (eM bC).symm.surjective.comp (φ_surjective H F b u hu0 huinv hΦ)
  have hinj := OrzechProperty.injective_of_surjective_endomorphism g hg
  intro x y hxy
  apply hinj
  show (eM bC).symm (φ H F b x) = (eM bC).symm (φ H F b y)
  rw [hxy]

include bC hu0 huinv hΦ in

theorem exists_subst_eq [Nonempty ι] (w : A B) (hw : δbar H F w = algebraMap (A B) (M C) w) :
    ∃ W : A B, subst u W = w := by
  classical
  obtain ⟨k₀⟩ := ‹Nonempty ι›
  obtain ⟨c, hc⟩ := hΦ (w * b k₀)
  refine ⟨c k₀, ?_⟩
  have h1 : φ H F b (fun k => subst u (c k)) = φ H F b (Pi.single k₀ w) := by
    rw [φ_subst H F b u hu0 huinv, ← hc, map_mul, hw, φ_apply]
    rw [Finset.sum_eq_single k₀]
    · simp [Algebra.smul_def]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ k₀) h
  have := congrFun (φ_injective H F bC b u hu0 huinv hΦ h1) k₀
  simp only [Pi.single_eq_same] at this
  exact this

end Rank

noncomputable section Uniq

variable {B : Type} [CommRing B] [IsNoetherianRing B]

theorem subst_injective (u : Fin 2 → A B) (hu0 : ∀ j, constantCoeff (u j) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (X i : A B) ^ N ∈ Ideal.span (Set.range u))
    {m : ℕ} (k₀ : Fin m) (bC : Module.Basis (Fin m) B (A B ⧸ Ideal.span (Set.range u)))
    (b : Fin m → A B) (hb : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range u)) (b k) = bC k) :
    Function.Injective (subst u : A B → A B) := by
  classical
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  suffices key : ∀ g : A B, subst u g = 0 → g = 0 by
    intro d₁ d₂ h
    rw [← sub_eq_zero]
    apply key
    rw [subst_sub hu, h, sub_self]
  intro g hg
  ext e
  apply eq_zero_of_localization
  intro J hJ
  let Bj := Localization.AtPrime J
  let f : B →+* Bj := algebraMap B Bj
  haveI : IsNoetherianRing Bj := IsLocalization.isNoetherianRing J.primeCompl Bj inferInstance
  let κ := IsLocalRing.ResidueField Bj
  let ρ : Fin 2 → A Bj := fun i => MvPowerSeries.map f (u i)
  have hρ0 : ∀ i, constantCoeff (ρ i) = 0 := fun i => by
    simp only [ρ, constantCoeff_map, hu0, map_zero]
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  let b' : Fin m → A Bj := fun k => MvPowerSeries.map f (b k)
  obtain ⟨eκ, heκ⟩ :=
    MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ) u hN
  have hfun : (fun i => MvPowerSeries.map (algebraMap B κ) (u i)) =
      fun i => MvPowerSeries.map (IsLocalRing.residue Bj) (ρ i) := by
    funext i
    show _ = MvPowerSeries.map (IsLocalRing.residue Bj) (MvPowerSeries.map f (u i))
    rw [← RingHom.comp_apply (MvPowerSeries.map (IsLocalRing.residue Bj)), ← MvPowerSeries.map_comp]
    rfl
  have hideal : Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap B κ) (u i)) =
      Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue Bj) (ρ i)) := by
    rw [hfun]
  let β : Module.Basis (Fin m) κ (MvPowerSeries (Fin 2) κ ⧸
      Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue Bj) (ρ i))) :=
    ((Algebra.TensorProduct.basis κ bC).map eκ.toLinearEquiv).map
      (Ideal.quotientEquivAlgOfEq κ hideal).toLinearEquiv
  have hβ : ∀ j, β j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue Bj) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue Bj) (b' j)) := by
    intro j
    simp only [β, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      AlgEquiv.toLinearEquiv_apply]
    rw [← hb j, heκ, one_smul, Ideal.quotientEquivAlgOfEq_mk]
    try rfl
  have h0 : subst ρ (0 : A Bj) = 0 := by
    rw [← coe_substAlgHom hρ, map_zero]
  have hrel : ∑ j, subst ρ ((Pi.single k₀ (MvPowerSeries.map f g) : Fin m → A Bj) j) * b' j =
      ∑ j, subst ρ ((0 : Fin m → A Bj) j) * b' j := by
    have hR : ∑ j, subst ρ ((0 : Fin m → A Bj) j) * b' j = 0 := by
      simp [h0]
    rw [hR, Finset.sum_eq_single k₀]
    · rw [Pi.single_eq_same]
      have : subst ρ (MvPowerSeries.map f g) = MvPowerSeries.map f (subst u g) := by
        rw [map_subst hu]
      rw [this, hg, map_zero, zero_mul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k₀) h
  have hloc := MvPowerSeries.eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue ρ hρ0 b' β hβ
    (Pi.single k₀ (MvPowerSeries.map f g)) 0 hrel
  have := congrFun hloc k₀
  simp only [Pi.single_eq_same, Pi.zero_apply] at this
  have := congrArg (coeff e) this
  rwa [coeff_map, map_zero] at this

end Uniq

end QAClosing

open QAClosing in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hfree : Module.Free B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    (huI : Ideal.span (Set.range u) = I)
    (w : MvPowerSeries (Fin 2) B)
    (hw : MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) :
    ∃! W : MvPowerSeries (Fin 2) B, MvPowerSeries.subst u W = w := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · have hall : ∀ f g : MvPowerSeries (Fin 2) B, f = g := fun f g => by
      ext e; exact Subsingleton.elim _ _
    exact ⟨0, hall _ _, fun W _ => hall _ _⟩
  subst huI
  haveI := hfin
  haveI := hfree

  let C := MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range u)
  let π : A B →ₐ[B] C := Ideal.Quotient.mkₐ B (Ideal.span (Set.range u))
  have H : Hyp π (Ideal.span (Set.range u)) :=
    ⟨fun a => Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_surjective, hnil⟩

  have hI1 : (1 : A B) ∉ Ideal.span (Set.range u) := by
    intro h1
    have hle : Ideal.span (Set.range u) ≤ RingHom.ker (MvPowerSeries.constantCoeff : A B →+* B) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hu0 j
    have := hle h1
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  haveI : Nontrivial C := ⟨⟨0, 1, fun h => hI1 ((Ideal.Quotient.eq_zero_iff_mem).1 h.symm)⟩⟩

  let bC := Module.finBasis B C
  have hne : Nonempty (Fin (Module.finrank B C)) := bC.index_nonempty
  obtain ⟨k₀⟩ := hne
  have hlift : ∀ k, ∃ a : A B, π a = bC k := fun k => Ideal.Quotient.mk_surjective (bC k)
  choose b hb using hlift

  have hgen : Submodule.span B (Set.range fun j =>
      Ideal.Quotient.mk (Ideal.span (Set.range u)) (b j)) = ⊤ := by
    have : (fun j => Ideal.Quotient.mk (Ideal.span (Set.range u)) (b j)) = fun j => bC j :=
      funext fun j => hb j
    rw [this]
    exact bC.span_eq
  have hΦ : ∀ f : A B, ∃ c : Fin (Module.finrank B C) → A B,
      f = ∑ k, MvPowerSeries.subst u (c k) * b k :=
    fun f => MvPowerSeries.exists_eq_sum_subst_mul_of_span_quotient_eq_top u hu0 b hgen f

  have huinv' : ∀ j, δbar H X.F (u j) = algebraMap (A B) (M C) (u j) :=
    fun j => δbar_eq_algebraMap_of_invariant H X.F (u j) (huinv j)
  have hw' : δbar H X.F w = algebraMap (A B) (M C) w :=
    δbar_eq_algebraMap_of_invariant H X.F w hw

  haveI : Nonempty (Fin (Module.finrank B C)) := ⟨k₀⟩
  obtain ⟨W, hW⟩ := exists_subst_eq H X.F bC b u hu0 huinv' hΦ w hw'
  refine ⟨W, hW, fun W' hW' => ?_⟩
  exact subst_injective u hu0 hnil k₀ bC b hb (hW'.trans hW.symm)

end S_CerednikDrinfeld_FormalODModule_existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free (solution)
