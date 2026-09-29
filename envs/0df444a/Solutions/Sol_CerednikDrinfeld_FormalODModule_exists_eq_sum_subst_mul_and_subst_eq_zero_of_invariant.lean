-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/04ba54f2-c238-598d-b5b8-9447c01f7b0d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace QB2aFG

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

theorem subst_map_algebraMap {m' : ℕ} {a : Fin m' → M C} (ha : HasSubst a) (c : MvPowerSeries (Fin m') B) :
    subst a (MvPowerSeries.map (algebraMap B C) c) = subst a c := by
  rw [map_algebraMap_eq_subst_X,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X l) ha]
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

theorem δbar_subst_eq_algebraMap {m' : ℕ} (u : Fin m' → A B) (hu0 : ∀ j, constantCoeff (u j) = 0)
    (huinv : ∀ j, δbar H F (u j) = algebraMap (A B) (M C) (u j)) (c : MvPowerSeries (Fin m') B) :
    δbar H F (subst u c) = algebraMap (A B) (M C) (subst u c) := by
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  rw [δbar_eq_subst, subst_comp_subst_apply hu (hasSubst_Fbar H F)]
  have h1 : (fun j : Fin m' => subst (fun j : Fin 2 => subst (aψ π) (F.toPowerSeries j)) (u j)) =
      fun j => algebraMap (A B) (M C) (u j) := by
    funext j
    rw [← δbar_eq_subst H, huinv]
  rw [h1]
  have halg : HasSubst (fun j : Fin m' => algebraMap (A B) (M C) (u j)) := by
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
variable {m' : ℕ} (u : Fin m' → A B) (hu0 : ∀ j, constantCoeff (u j) = 0)
  (huinv : ∀ j, δbar H F (u j) = algebraMap (A B) (M C) (u j))
  (hΦ : ∀ f : A B, ∃ c : ι → MvPowerSeries (Fin m') B, f = ∑ k, subst u (c k) * b k)

def φ : (ι → A B) →ₗ[A B] M C :=
  (Pi.basisFun (A B) ι).constr (A B) fun k => δbar H F (b k)

theorem φ_apply (a : ι → A B) : φ H F b a = ∑ k, a k • δbar H F (b k) := by
  simp [φ, Module.Basis.constr_apply_fintype]

include hu0 huinv in
theorem φ_subst (c : ι → MvPowerSeries (Fin m') B) :
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

end Rank

section CN
open MvPowerSeries

variable {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]

theorem smul_top_pow_succ (k : ℕ) : I ^ k • (I • (⊤ : Submodule R M)) = I ^ (k + 1) • ⊤ := by
  rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]

theorem step {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M))
    (k : ℕ) (x : M) (hx : x ∈ I ^ k • (⊤ : Submodule R M)) :
    ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧ x - ∑ j, a j • m j ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
  classical
  induction hx using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨a, ha⟩ := hgen y
    refine ⟨fun j => r * a j, fun j => Ideal.mul_mem_right _ _ hr, ?_⟩
    have : r • y - ∑ j, (r * a j) • m j = r • (y - ∑ j, a j • m j) := by
      rw [smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (smul_smul r (a j) (m j)).symm
    rw [this, ← smul_top_pow_succ]
    exact Submodule.smul_mem_smul hr ha
  | add x hx y hy ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨a', ha', hay⟩ := ihy
    refine ⟨a + a', fun j => Ideal.add_mem _ (ha j) (ha' j), ?_⟩
    have : x + y - ∑ j, (a + a') j • m j = (x - ∑ j, a j • m j) + (y - ∑ j, a' j • m j) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
    rw [this]
    exact Submodule.add_mem _ hax hay

theorem exists_eq_sum_smul [IsAdicComplete I R] [IsHausdorff I M] {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M)) (x : M) :
    ∃ c : Fin d → R, x = ∑ j, c j • m j := by
  classical
  have hstep : ∀ (k : ℕ) (z : {z : M // z ∈ I ^ k • (⊤ : Submodule R M)}),
      ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧ z.1 - ∑ j, a j • m j ∈ I ^ (k + 1) • (⊤ : Submodule R M) :=
    fun k z => step I m hgen k z.1 z.2
  choose A hAI hAnext using hstep
  let seq : (k : ℕ) → {z : M // z ∈ I ^ k • (⊤ : Submodule R M)} :=
    fun k => Nat.rec (motive := fun k => {z : M // z ∈ I ^ k • (⊤ : Submodule R M)})
      ⟨x, by rw [pow_zero, one_smul]; exact Submodule.mem_top⟩
      (fun k z => ⟨z.1 - ∑ j, A k z j • m j, hAnext k z⟩) k
  have hseq0 : (seq 0).1 = x := rfl
  have hseqS : ∀ k, (seq (k + 1)).1 = (seq k).1 - ∑ j, A k (seq k) j • m j := fun k => rfl
  let a : ℕ → Fin d → R := fun k => A k (seq k)
  have haI : ∀ k j, a k j ∈ I ^ k := fun k j => hAI k (seq k) j
  let s : ℕ → Fin d → R := fun K j => ∑ k ∈ Finset.range K, a k j
  have hpartial : ∀ K, x = ∑ j, s K j • m j + (seq K).1 := by
    intro K
    induction K with
    | zero => simp [s, hseq0]
    | succ K ih =>
      rw [hseqS, ih]
      simp only [s, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      abel
  have hcauchy : ∀ j, ∀ {m' n' : ℕ}, m' ≤ n' → s m' j ≡ s n' j [SMOD (I ^ m' • ⊤ : Submodule R R)] := by
    intro j m' n' hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have : s m' j - s n' j = -∑ k ∈ Finset.Ico m' n', a k j := by
      simp only [s]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [this, neg_mem_iff]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1 (haI k j)
  have hlim : ∀ j, ∃ c : R, ∀ K, s K j ≡ c [SMOD (I ^ K • ⊤ : Submodule R R)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose c hc using hlim
  refine ⟨c, ?_⟩
  apply eq_of_sub_eq_zero
  refine IsHausdorff.haus' (I := I) _ fun K => ?_
  rw [SModEq.sub_mem, sub_zero]
  have hdiff : x - ∑ j, c j • m j = (seq K).1 - ∑ j, (c j - s K j) • m j := by
    conv_lhs => rw [hpartial K]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  refine Submodule.sub_mem _ (seq K).2 (Submodule.sum_mem _ fun j _ => ?_)
  have hcj : c j - s K j ∈ I ^ K := by
    have := (hc j K).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  exact Submodule.smul_mem_smul hcj Submodule.mem_top

end CN

section Low

variable {σ : Type} {R : Type} [CommRing R]

def lowVanishing (σ : Type) (R : Type) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {q | ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d q = 0}
  add_mem' {a b} ha hb := fun d hd => by rw [map_add, ha d hd, hb d hd, add_zero]
  zero_mem' := fun d _ => by simp
  smul_mem' c {q} hq := fun d hd => by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have : x.2.degree < N := by
      have h := congrArg Finsupp.degree hx'
      rw [(map_add Finsupp.degree)] at h
      omega
    rw [hq x.2 this, mul_zero]

theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨s, rfl⟩ d hd
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
  subst this
  exact MvPowerSeries.coeff_zero_X s

theorem lowVanishing_mul_le (a b : ℕ) : lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro p hp q hq d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)
  rw [(map_add Finsupp.degree)] at hx'
  by_cases h1 : x.1.degree < a
  · rw [hp x.1 h1, zero_mul]
  · have h2 : x.2.degree < b := by omega
    rw [hq x.2 h2, mul_zero]

theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ d hd
    exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le N 1)

theorem eq_zero_of_forall_mem_pow_span_X (q : MvPowerSeries σ R)
    (hq : ∀ N, q ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N) : q = 0 := by
  ext d
  rw [map_zero]
  exact pow_span_X_le_lowVanishing (d.degree + 1) (hq _) d (Nat.lt_succ_self _)

end Low

section ViaRho

variable {B : Type} [CommRing B] {m : ℕ} {τ : Type}

def ViaRho (ρ : Fin m → MvPowerSeries τ B) (_hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) : Type :=
  MvPowerSeries τ B

variable (ρ : Fin m → MvPowerSeries τ B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)

noncomputable scoped instance : AddCommGroup (ViaRho ρ hρ0) := inferInstanceAs (AddCommGroup (MvPowerSeries τ B))

noncomputable def toV : MvPowerSeries τ B ≃+ ViaRho ρ hρ0 := AddEquiv.refl _

include hρ0 in
theorem subst_one' : MvPowerSeries.subst ρ (1 : MvPowerSeries (Fin m) B) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_one]

include hρ0 in
theorem subst_mul' (a c : MvPowerSeries (Fin m) B) :
    MvPowerSeries.subst ρ (a * c) = MvPowerSeries.subst ρ a * MvPowerSeries.subst ρ c := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_mul]

include hρ0 in
theorem subst_add' (a c : MvPowerSeries (Fin m) B) :
    MvPowerSeries.subst ρ (a + c) = MvPowerSeries.subst ρ a + MvPowerSeries.subst ρ c := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_add]

include hρ0 in
theorem subst_zero' : MvPowerSeries.subst ρ (0 : MvPowerSeries (Fin m) B) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_zero]

noncomputable scoped instance instModule : Module (MvPowerSeries (Fin m) B) (ViaRho ρ hρ0) where
  smul c f := toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)
  one_smul f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ 1 * (toV ρ hρ0).symm f) = f
    rw [subst_one' ρ hρ0, one_mul]; rfl
  mul_smul a c f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ (a * c) * (toV ρ hρ0).symm f) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm (toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)))
    rw [subst_mul' ρ hρ0, AddEquiv.symm_apply_apply, mul_assoc]
  smul_zero a := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm 0) = 0
    rw [map_zero, mul_zero, map_zero]
  smul_add a f g := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm (f + g)) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm f) + toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm g)
    rw [map_add, mul_add, map_add]
  add_smul a c f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ (a + c) * (toV ρ hρ0).symm f) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm f) + toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)
    rw [subst_add' ρ hρ0, add_mul, map_add]
  zero_smul f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ 0 * (toV ρ hρ0).symm f) = 0
    rw [subst_zero' ρ hρ0, zero_mul, map_zero]

private theorem _root_.QB2aFG.smul_def (c : MvPowerSeries (Fin m) B) (f : ViaRho ρ hρ0) :
    c • f = toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f) := rfl

p2m_export "QB2aFG" "smul_def"
end ViaRho

section Surj

variable {B : Type} [CommRing B]

theorem surj_rect {m : ℕ} {τ : Type} [Fintype τ] [DecidableEq τ]
    (ρ : Fin m → MvPowerSeries τ B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    {d : Type} [Fintype d] (b : d → MvPowerSeries τ B)
    (hgen : Submodule.span B (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j))) = ⊤)
    (f : MvPowerSeries τ B) :
    ∃ c : d → MvPowerSeries (Fin m) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical

  obtain ⟨n, e⟩ : ∃ n, Nonempty (d ≃ Fin n) := ⟨Fintype.card d, ⟨Fintype.equivFin d⟩⟩
  obtain ⟨e⟩ := e
  set I : Ideal (MvPowerSeries (Fin m) B) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin m → MvPowerSeries (Fin m) B)) with hI
  set J : Ideal (MvPowerSeries τ B) :=
    Ideal.span (Set.range (MvPowerSeries.X : τ → MvPowerSeries τ B)) with hJ
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  have hρx : ∀ i, ρ i ∈ J := fun i => mem_span_X_of_constantCoeff_eq_zero (ρ i) (hρ0 i)

  have hmapI : ∀ k : ℕ, ∀ c ∈ I ^ k, MvPowerSeries.subst ρ c ∈ J ^ k := by
    intro k c hc
    let φ : MvPowerSeries (Fin m) B →+* MvPowerSeries τ B :=
      (MvPowerSeries.substAlgHom hsub : MvPowerSeries (Fin m) B →ₐ[B] _).toRingHom
    have hφ : ∀ g, φ g = MvPowerSeries.subst ρ g := fun g => by
      show (MvPowerSeries.substAlgHom hsub) g = _
      rw [← MvPowerSeries.coe_substAlgHom hsub]
    have h1 : I.map φ ≤ J := by
      rw [hI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hφ, MvPowerSeries.subst_X hsub]
      exact hρx i
    have h2 : (I ^ k).map φ ≤ J ^ k := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 k
    have h3 := h2 (Ideal.mem_map_of_mem φ hc)
    rwa [hφ] at h3
  have hsmul_le : ∀ (k : ℕ) (z : ViaRho ρ hρ0), z ∈ I ^ k • (⊤ : Submodule (MvPowerSeries (Fin m) B) (ViaRho ρ hρ0)) →
      (toV ρ hρ0).symm z ∈ J ^ k := by
    intro k z hz
    induction hz using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      rw [smul_def ρ hρ0]
      change MvPowerSeries.subst ρ r * (toV ρ hρ0).symm y ∈ J ^ k
      exact Ideal.mul_mem_right _ _ (hmapI k r hr)
    | add x hx y hy ihx ihy =>
      change (toV ρ hρ0).symm x + (toV ρ hρ0).symm y ∈ J ^ k
      exact Ideal.add_mem _ ihx ihy
  haveI : IsHausdorff I (ViaRho ρ hρ0) := ⟨fun z hz => by
    have : (toV ρ hρ0).symm z = 0 := eq_zero_of_forall_mem_pow_span_X _ fun N => by
      have h := hz N
      rw [SModEq.sub_mem, sub_zero] at h
      exact hsmul_le N z h
    exact this⟩
  have hρI : ∀ w ∈ Ideal.span (Set.range ρ), toV ρ hρ0 w ∈ I • (⊤ : Submodule (MvPowerSeries (Fin m) B) (ViaRho ρ hρ0)) := by
    intro w hw
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hw
    change toV ρ hρ0 (∑ i, g i * ρ i) ∈ _
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : toV ρ hρ0 (g i * ρ i) = (MvPowerSeries.X i : MvPowerSeries (Fin m) B) • toV ρ hρ0 (g i) := by
      rw [smul_def ρ hρ0, MvPowerSeries.subst_X hsub, mul_comm]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top

  let b' : Fin n → MvPowerSeries τ B := fun j => b (e.symm j)
  have hgen' : ∀ z : ViaRho ρ hρ0, ∃ a : Fin n → MvPowerSeries (Fin m) B,
      z - ∑ j, a j • toV ρ hρ0 (b' j) ∈ I • (⊤ : Submodule (MvPowerSeries (Fin m) B) (ViaRho ρ hρ0)) := by
    intro z
    have hmem : Ideal.Quotient.mk (Ideal.span (Set.range ρ)) ((toV ρ hρ0).symm z) ∈
        Submodule.span B (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)) := by
      rw [hgen]; exact Submodule.mem_top
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hmem
    refine ⟨fun j => (MvPowerSeries.C (β (e.symm j)) : MvPowerSeries (Fin m) B), ?_⟩
    have hdiff : (toV ρ hρ0).symm z - ∑ k, (MvPowerSeries.C (β k) : MvPowerSeries τ B) * b k ∈ Ideal.span (Set.range ρ) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, sub_eq_zero, ← hβ]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ)) ((MvPowerSeries.C (β k) : MvPowerSeries τ B) * b k) =
          β k • Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ)) (b k) := by
        rw [← MvPowerSeries.smul_eq_C_mul, map_smul]
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using hk.symm
    have hsm : ∀ k, (MvPowerSeries.C (β k) : MvPowerSeries (Fin m) B) • toV ρ hρ0 (b k) =
        toV ρ hρ0 ((MvPowerSeries.C (β k) : MvPowerSeries τ B) * b k) := fun k => by
      rw [smul_def ρ hρ0, MvPowerSeries.subst_C]
      rfl
    have hre : ∑ j, (MvPowerSeries.C (β (e.symm j)) : MvPowerSeries (Fin m) B) • toV ρ hρ0 (b' j) =
        ∑ k, (MvPowerSeries.C (β k) : MvPowerSeries (Fin m) B) • toV ρ hρ0 (b k) :=
      Equiv.sum_comp e.symm (fun k => (MvPowerSeries.C (β k) : MvPowerSeries (Fin m) B) • toV ρ hρ0 (b k))
    have : z - ∑ j, (MvPowerSeries.C (β (e.symm j)) : MvPowerSeries (Fin m) B) • toV ρ hρ0 (b' j) =
        toV ρ hρ0 ((toV ρ hρ0).symm z - ∑ k, (MvPowerSeries.C (β k) : MvPowerSeries τ B) * b k) := by
      rw [hre, map_sub, map_sum, AddEquiv.apply_symm_apply]
      congr 1
      exact Finset.sum_congr rfl fun k _ => hsm k
    rw [this]
    exact hρI _ hdiff
  obtain ⟨c, hc⟩ := exists_eq_sum_smul I (fun j => toV ρ hρ0 (b' j)) hgen' (toV ρ hρ0 f)
  refine ⟨fun k => c (e k), ?_⟩
  apply (toV ρ hρ0).injective
  rw [hc, map_sum, ← Equiv.sum_comp e (fun j => c j • toV ρ hρ0 (b' j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_def ρ hρ0]
  show toV ρ hρ0 (MvPowerSeries.subst ρ (c (e k)) * b (e.symm (e k))) = _
  rw [Equiv.symm_apply_apply]

end Surj

end QB2aFG
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant.QB2aFG"

open MvPowerSeries QB2aFG in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    {ι : Type} [Fintype ι] (bC : Module.Basis ι B (MvPowerSeries (Fin 2) B ⧸ I))
    (b : ι → MvPowerSeries (Fin 2) B) (hb : ∀ k, Ideal.Quotient.mk I (b k) = bC k)
    {m : ℕ} (u : Fin m → MvPowerSeries (Fin 2) B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    (huI : Ideal.span (Set.range u) = I) :
    (∀ f : MvPowerSeries (Fin 2) B, ∃ c : ι → MvPowerSeries (Fin m) B,
        f = ∑ k, MvPowerSeries.subst u (c k) * b k) ∧
    (∀ c : ι → MvPowerSeries (Fin m) B,
        ∑ k, MvPowerSeries.subst u (c k) * b k = 0 → ∀ k, MvPowerSeries.subst u (c k) = 0) := by
  classical
  subst huI

  let C := MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range u)
  let π : A B →ₐ[B] C := Ideal.Quotient.mkₐ B (Ideal.span (Set.range u))
  have H : Hyp π (Ideal.span (Set.range u)) :=
    ⟨fun a => Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_surjective, hnil⟩

  have hgen : Submodule.span B (Set.range fun j =>
      Ideal.Quotient.mk (Ideal.span (Set.range u)) (b j)) = ⊤ := by
    have : (fun j => Ideal.Quotient.mk (Ideal.span (Set.range u)) (b j)) = fun j => bC j :=
      funext fun j => hb j
    rw [this]
    exact bC.span_eq
  have hΦ : ∀ f : A B, ∃ c : ι → MvPowerSeries (Fin m) B,
      f = ∑ k, MvPowerSeries.subst u (c k) * b k :=
    fun f => surj_rect u hu0 b hgen f
  refine ⟨hΦ, ?_⟩

  have huinv' : ∀ j, δbar H X.F (u j) = algebraMap (A B) (M C) (u j) :=
    fun j => δbar_eq_algebraMap_of_invariant H X.F (u j) (huinv j)
  intro c hc k
  have h1 : φ H X.F b (fun k => MvPowerSeries.subst u (c k)) = φ H X.F b 0 := by
    rw [φ_subst H X.F b u hu0 huinv', hc, map_zero, map_zero]
  have h2 := φ_injective H X.F bC b u hu0 huinv' hΦ h1
  exact congrFun h2 k

end S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant (solution)
