-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_add_typed_of_primitive_mod_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/dd273c6a-558e-5e5a-b5ef-ab24d28c2d70

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries

set_option autoImplicit false

universe u

noncomputable section

namespace R3Sol

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

section Generic

variable {R : Type*} [CommRing R] {σ : Type*}

theorem exists_eq_sum_X_pow_mul' [DecidableEq σ] (e : σ → ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s < e s) → coeff d f = 0) →
      ∃ r : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s ^ e s * r s := by
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
    let f₀ : MvPowerSeries σ R := fun d => if d s < e s then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s < e s then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ^ e s ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨r, hr⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update r s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t ^ e t * Function.update r s q' t = ∑ t ∈ T, X t ^ e t * r t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hr, ← hq']
    ring

theorem subst_mem_span {τ : Type*} [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries τ R)
    (hφ : ∀ s, constantCoeff (φ s) = 0) (g : MvPowerSeries σ R) (hg : constantCoeff g = 0) :
    subst φ g ∈ Ideal.span (Set.range φ) := by
  have hs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  obtain ⟨r, hr⟩ := exists_eq_sum_X_pow_mul' (R := R) (fun _ => 1) Finset.univ g (fun d hd => by
    have hd0 : d = 0 := by
      ext s
      have h1 : d s < 1 := hd s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [hd0, coeff_zero_eq_constantCoeff_apply]
    exact hg)
  rw [hr, ← coe_substAlgHom hs, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, pow_one, coe_substAlgHom hs, subst_X hs s]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem subst_mem_of_mem_span {τ ι : Type*} (φ : σ → MvPowerSeries τ R) (hφ : HasSubst φ)
    (gen : ι → MvPowerSeries σ R) (J : Ideal (MvPowerSeries τ R)) (hgen : ∀ i, subst φ (gen i) ∈ J)
    {f : MvPowerSeries σ R} (hf : f ∈ Ideal.span (Set.range gen)) : subst φ f ∈ J := by
  rw [← coe_substAlgHom hφ]
  have : Ideal.map (substAlgHom hφ).toRingHom (Ideal.span (Set.range gen)) ≤ J := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show (substAlgHom hφ) (gen i) ∈ J
    rw [coe_substAlgHom]
    exact hgen i
  exact this (Ideal.mem_map_of_mem _ hf)

theorem smul_mem_ideal' {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A) (c : R) {x : A} (hx : x ∈ J) :
    c • x ∈ J := by
  rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx

end Generic

section Main

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

abbrev I : Ideal (MvPowerSeries (Fin 2) k) := Ideal.span (Set.range (X₀.F.nthSeries q))

abbrev XL : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun t => X (Sum.inl t)
abbrev XR : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun t => X (Sum.inr t)

abbrev I₂ : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) k) :=
  Ideal.span (Set.range (Sum.elim (fun l => subst (XL (k := k)) (X₀.F.nthSeries q l))
    (fun l => subst (XR (k := k)) (X₀.F.nthSeries q l))))

theorem constantCoeff_nth (i : Fin 2) : constantCoeff (X₀.F.nthSeries q i) = 0 :=
  MvFormalGroup.constantCoeff_nthSeries X₀.F q i

theorem constantCoeff_act (a : Zp2 q) (i : Fin 2) : constantCoeff (X₀.act a i) = 0 := (X₀.isLawHom_act a).1 i
theorem constantCoeff_varpi (i : Fin 2) : constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1 i

def CommQ (u : Series k) : Prop :=
  (∀ i, constantCoeff (u i) = 0) ∧ ∀ i, subst u (X₀.F.nthSeries q i) = subst (X₀.F.nthSeries q) (u i)

theorem CommQ.subst_mem {u : Series k} (hu : CommQ X₀ u) {f : MvPowerSeries (Fin 2) k} (hf : f ∈ I X₀) :
    subst u f ∈ I X₀ := by
  refine subst_mem_of_mem_span u (hasSubst_of_constantCoeff_zero hu.1) _ _ (fun i => ?_) hf
  rw [hu.2 i]
  exact subst_mem_span _ (constantCoeff_nth X₀) _ (hu.1 i)

theorem commQ_act (a : Zp2 q) : CommQ X₀ (X₀.act a) := by
  refine ⟨constantCoeff_act X₀ a, fun i => ?_⟩
  have h1 : X₀.act ((q : Zp2 q) * a) = (X₀.act (q : Zp2 q)).comp (X₀.act a) := X₀.act_mul _ _
  have h2 : X₀.act (a * (q : Zp2 q)) = (X₀.act a).comp (X₀.act (q : Zp2 q)) := X₀.act_mul _ _
  rw [mul_comm, h2, FormalODModule.act_natCast] at h1
  exact (congrFun h1 i).symm

theorem commQ_varpi : CommQ X₀ X₀.varpi := by
  refine ⟨constantCoeff_varpi X₀, fun i => ?_⟩
  have h := X₀.varpi_comp_act (q : Zp2 q)
  rw [map_natCast, FormalODModule.act_natCast] at h
  exact (congrFun h i).symm

theorem CommQ.comp {u v : Series k} (hu : CommQ X₀ u) (hv : CommQ X₀ v) : CommQ X₀ (u.comp v) := by
  have hsv := hasSubst_of_constantCoeff_zero hv.1
  have hsu := hasSubst_of_constantCoeff_zero hu.1
  refine ⟨fun i => constantCoeff_subst_eq_zero hsv hv.1 (hu.1 i), fun i => ?_⟩
  show subst (fun j => subst v (u j)) (X₀.F.nthSeries q i) = subst (X₀.F.nthSeries q) (subst v (u i))
  rw [← subst_comp_subst_apply hsu hsv, hu.2 i, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_nth X₀)) hsv,
    show (fun j => subst v (X₀.F.nthSeries q j)) = fun j => subst (X₀.F.nthSeries q) (v j) from funext hv.2,
    ← subst_comp_subst_apply hsv (hasSubst_of_constantCoeff_zero (constantCoeff_nth X₀))]

def Prim (h : MvPowerSeries (Fin 2) k) : Prop := constantCoeff h = 0 ∧ X₀.F.addCoboundary h ∈ I₂ X₀

theorem subst_addVia_sub_mem {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) {u v : Series k}
    (hu : CommQ X₀ u) (hv : CommQ X₀ v) :
    subst (Series.addVia X₀.F u v) h - (subst u h + subst v h) ∈ I X₀ := by
  have hsu := hasSubst_of_constantCoeff_zero hu.1
  have hsv := hasSubst_of_constantCoeff_zero hv.1
  have huv0 : ∀ s, constantCoeff (Sum.elim u v s) = 0 := by rintro (j | j); exacts [hu.1 j, hv.1 j]
  have hsuv : HasSubst (Sum.elim u v) := hasSubst_of_constantCoeff_zero huv0

  have e1 : subst (Series.addVia X₀.F u v) h = subst (Sum.elim u v) (subst X₀.F.toPowerSeries h) := by
    rw [subst_comp_subst_apply X₀.F.hasSubst_toPowerSeries hsuv]; rfl
  have e2 : subst X₀.F.toPowerSeries h = X₀.F.addCoboundary h + subst (XL (k := k)) h + subst (XR (k := k)) h := by
    rw [MvFormalGroup.addCoboundary]; ring
  have eL : subst (Sum.elim u v) (subst (XL (k := k)) h) = subst u h := by
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) hsuv]
    congr 1; funext t; exact subst_X hsuv _
  have eR : subst (Sum.elim u v) (subst (XR (k := k)) h) = subst v h := by
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) hsuv]
    congr 1; funext t; exact subst_X hsuv _
  have e3 : subst (Sum.elim u v) (X₀.F.addCoboundary h + subst (XL (k := k)) h + subst (XR (k := k)) h) =
      subst (Sum.elim u v) (X₀.F.addCoboundary h) + subst u h + subst v h := by
    rw [← coe_substAlgHom hsuv, map_add, map_add, coe_substAlgHom hsuv, eL, eR]
  rw [e1, e2, e3, show ∀ a b c : MvPowerSeries (Fin 2) k, a + b + c - (b + c) = a from fun a b c => by ring]

  refine subst_mem_of_mem_span _ hsuv _ _ (fun s => ?_) hh.2
  rcases s with l | l
  · show subst (Sum.elim u v) (subst XL (X₀.F.nthSeries q l)) ∈ I X₀
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) hsuv,
      show (fun t => subst (Sum.elim u v) (XL (k := k) t)) = u from funext fun t => subst_X hsuv _, hu.2 l]
    exact subst_mem_span _ (constantCoeff_nth X₀) _ (hu.1 l)
  · show subst (Sum.elim u v) (subst XR (X₀.F.nthSeries q l)) ∈ I X₀
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) hsuv,
      show (fun t => subst (Sum.elim u v) (XR (k := k) t)) = v from funext fun t => subst_X hsuv _, hv.2 l]
    exact subst_mem_span _ (constantCoeff_nth X₀) _ (hv.1 l)

end Main

end R3Sol

noncomputable section

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R]

namespace C1Kit

variable {τ : Type*} (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

theorem constantCoeff_XL (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem constantCoeff_XR (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem symm_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    subst (Sum.elim b a) Γ = subst (Sum.elim a b) Γ := by
  have hT : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := R) (Sum.elim a b)) hΓ.symm
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim a b) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  exact key

theorem cocycle_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b c : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c) Γ
        + subst (Sum.elim a b) Γ
      = subst (Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j)) Γ
        + subst (Sum.elim b c) Γ := by
  have hT0 : ∀ s : Fin g ⊕ (Fin g ⊕ Fin g),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
  have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hB := hasSubst_of_constantCoeff_zero hzB
  have hC := hasSubst_of_constantCoeff_zero hzC
  have hA : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hA' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
  have key := congrArg (subst (R := R) (Sum.elim a (Sum.elim b c))) hΓ.cocycle
  rw [subst_add hT, subst_add hT, subst_comp_subst_apply hA hT, subst_comp_subst_apply hA' hT,
    subst_comp_subst_apply hB hT, subst_comp_subst_apply hC hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hA'fam, hBfam, hCfam] at key
  exact key

theorem four_term [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ) {a b c d : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j))
        fun j => subst (Sum.elim c d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a b) Γ + subst (Sum.elim c d) Γ
      = subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j))
        fun j => subst (Sum.elim b d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a c) Γ + subst (Sum.elim b d) Γ := by
  have hab := constantCoeff_subst_elim F ha hb
  have hac := constantCoeff_subst_elim F ha hc
  have e1 := cocycle_elim F hΓ hab hc hd
  have e2 := cocycle_elim F hΓ hac hb hd
  have e3 := cocycle_elim F hΓ ha hb hc
  have e4 := cocycle_elim F hΓ ha hc hb
  have hcb : (fun j => subst (Sum.elim c b) (F.toPowerSeries j))
      = fun j => subst (Sum.elim b c) (F.toPowerSeries j) :=
    funext fun j => subst_elim_comm F hc hb j
  rw [hcb, symm_elim F hΓ hb hc] at e4
  have h6 : (fun j => subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c)
        (F.toPowerSeries j))
      = fun j => subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j)) b)
        (F.toPowerSeries j) := by
    funext j
    rw [subst_elim_assoc F ha hb hc j, ← hcb, ← subst_elim_assoc F ha hc hb j]
  rw [h6] at e1
  linear_combination e2 - e1 + e3 - e4

end C1Kit

end MvFormalGroup

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

noncomputable abbrev inL (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

noncomputable abbrev inR (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

theorem hasSubst_XL : HasSubst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem constantCoeff_inL (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inL φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (hφ i)

theorem constantCoeff_inR (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inR φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (hφ i)

theorem inL_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inL (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inL φ) (inL ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem inR_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inR (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inR φ) (inR ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XL_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inL φ) (inL ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XR_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inR φ) (inR ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_law_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i))
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst F.toPowerSeries (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (fun i => subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
          fun i => subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) F.hasSubst_toPowerSeries]
  congr 1
  funext s; rcases s with j | j
  · exact hφF j
  · exact hψF j

theorem pull_addVia [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) :
    subst (Sum.elim (inL fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
        (inR fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))) Γ
      = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL ψ) (inR ψ)) Γ
        + F.addCoboundary (subst (Sum.elim φ ψ) Γ) := by
  rw [inL_addVia F hφ hψ, inR_addVia F hφ hψ, addCoboundary, subst_law_subst_elim F hφ hψ hφF hψF,
    subst_XL_subst_elim hφ hψ, subst_XR_subst_elim hφ hψ]
  have h4 := four_term F hΓ (constantCoeff_inL hφ) (constantCoeff_inL hψ) (constantCoeff_inR hφ)
    (constantCoeff_inR hψ)
  linear_combination h4

theorem constantCoeff_subst_elim_cocycle (hΓ : F.IsSymmTwoCocycle Γ) {τ : Type*}
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    (subst (Sum.elim a b) Γ).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim ha hb) (by rintro (s | s); exacts [ha s, hb s])
    hΓ.constantCoeff_eq_zero

end MvFormalGroup.C1Kit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}
variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem subst_subst_pull {τ : Type*} {T : Fin g ⊕ Fin g → MvPowerSeries τ R} (hT : HasSubst T)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst T (subst (Sum.elim (inL φ) (inR φ)) f)
      = subst (Sum.elim (fun i => subst (fun m => T (Sum.inl m)) (φ i))
          fun i => subst (fun m => T (Sum.inr m)) (φ i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)) hT]
  congr 1
  funext s; rcases s with j | j
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XL hT]
    congr 1; funext m; exact subst_X hT _
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XR hT]
    congr 1; funext m; exact subst_X hT _

theorem pull_comp (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => subst ψ (φ i)) (inR fun i => subst ψ (φ i))) f
      = subst (Sum.elim (inL ψ) (inR ψ)) (subst (Sum.elim (inL φ) (inR φ)) f) := by
  rw [subst_subst_pull (hasSubst_elim (constantCoeff_inL hψ) (constantCoeff_inR hψ)) hφ]
  congr 1
  funext s; rcases s with j | j
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XL]
    rfl
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XR]
    rfl

theorem pull_X (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)) f = f := by
  have h : Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)
      = (X : Fin g ⊕ Fin g → MvPowerSeries (Fin g ⊕ Fin g) R) := by
    funext s; rcases s with j | j
    · exact subst_X hasSubst_XL j
    · exact subst_X hasSubst_XR j
  rw [h, subst_self]; rfl

theorem symm_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      = subst (Sum.elim (inL φ) (inR φ)) Γ := by
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  rw [subst_subst_pull hswap hφ]
  exact symm_elim F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)

section ThreeBlocks

noncomputable abbrev B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inl l)
noncomputable abbrev B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inl l))
noncomputable abbrev B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inr l))

theorem cB1 (l : Fin g) : ((B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB2 (l : Fin g) : ((B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB3 (l : Fin g) : ((B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _

noncomputable abbrev atB (B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
    (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R :=
  fun i => subst B (φ i)

theorem constantCoeff_atB {B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hB : ∀ l, (B l).constantCoeff = 0) (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (atB B φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hB) hB (hφ i)

theorem subst_lawpair (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    {Bi Bj : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hBi : ∀ l, (Bi l).constantCoeff = 0) (hBj : ∀ l, (Bj l).constantCoeff = 0) (i : Fin g) :
    subst (fun m => subst (Sum.elim Bi Bj) (F.toPowerSeries m)) (φ i)
      = subst (Sum.elim (atB Bi φ) (atB Bj φ)) (F.toPowerSeries i) := by
  rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_elim hBi hBj), hφF i,
    subst_subst_pull (hasSubst_elim hBi hBj) hφ]
  rfl

theorem cocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ) := by
  have hB12 : HasSubst (Sum.elim (B1 (g := g) (R := R)) B2) := hasSubst_elim cB1 cB2
  have hB23 : HasSubst (Sum.elim (B2 (g := g) (R := R)) B3) := hasSubst_elim cB2 cB3
  have hA : HasSubst (Sum.elim (fun j => subst (Sum.elim (B1 (g := g) (R := R)) B2) (F.toPowerSeries j)) B3) :=
    hasSubst_elim (constantCoeff_subst_elim F cB1 cB2) cB3
  have hA' : HasSubst (Sum.elim B1 fun j => subst (Sum.elim (B2 (g := g) (R := R)) B3) (F.toPowerSeries j)) :=
    hasSubst_elim cB1 (constantCoeff_subst_elim F cB2 cB3)
  show subst (Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3) _
      + subst (Sum.elim B1 B2) _
      = subst (Sum.elim B1 fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) _ + subst (Sum.elim B2 B3) _
  rw [subst_subst_pull hA hφ, subst_subst_pull hB12 hφ, subst_subst_pull hA' hφ, subst_subst_pull hB23 hφ]
  have k := cocycle_elim F hΓ (constantCoeff_atB cB1 hφ) (constantCoeff_atB cB2 hφ) (constantCoeff_atB cB3 hφ)
  have h1 : (fun i => subst (fun m => Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3 (Sum.inl m))
      (φ i)) = fun i => subst (Sum.elim (atB B1 φ) (atB B2 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB1 cB2 i
  have h2 : (fun i => subst (fun m => Sum.elim B1 (fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) (Sum.inr m))
      (φ i)) = fun i => subst (Sum.elim (atB B2 φ) (atB B3 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB2 cB3 i
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
  rw [h1, h2]
  exact k

end ThreeBlocks

theorem isSymmTwoCocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    F.IsSymmTwoCocycle (subst (Sum.elim (inL φ) (inR φ)) Γ) where
  constantCoeff_eq_zero := constantCoeff_subst_elim_cocycle F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  symm := symm_pull F hΓ hφ
  cocycle := cocycle_pull F hΓ hφ hφF

theorem pull_addCoboundary (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (g₁ : MvPowerSeries (Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (F.addCoboundary g₁) = F.addCoboundary (subst φ g₁) := by
  have hP : HasSubst (Sum.elim (inL φ) (inR φ)) := hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  rw [addCoboundary, addCoboundary, subst_sub hP, subst_sub hP,
    subst_comp_subst_apply F.hasSubst_toPowerSeries hP, subst_comp_subst_apply hasSubst_XL hP,
    subst_comp_subst_apply hasSubst_XR hP, subst_comp_subst_apply hφs F.hasSubst_toPowerSeries,
    subst_comp_subst_apply hφs hasSubst_XL, subst_comp_subst_apply hφs hasSubst_XR]
  congr 2
  · congr 1; funext i; exact (hφF i).symm
  · congr 1; funext m; exact subst_X hP _
  · congr 1; funext m; exact subst_X hP _

end MvFormalGroup.C1Kit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] {φ : Fin g → MvPowerSeries (Fin g) R}

theorem hasSubst_pull (hφ : ∀ i, (φ i).constantCoeff = 0) : HasSubst (Sum.elim (inL φ) (inR φ)) :=
  hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)

theorem pull_smul_add (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ + Γ')
      = c • subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_add, map_smul]

theorem pull_add (hφ : ∀ i, (φ i).constantCoeff = 0) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (Γ + Γ') = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' :=
  subst_add (hasSubst_pull hφ) Γ Γ'

theorem pull_smul (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ) = c • subst (Sum.elim (inL φ) (inR φ)) Γ := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_smul]

theorem pull_zero (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (inL φ) (inR φ)) (0 : MvPowerSeries (Fin g ⊕ Fin g) R) = 0 := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_zero]

end MvFormalGroup.C1Kit

namespace C1cKit

open WittVector

variable (q : ℕ) [hq : Fact q.Prime]

theorem exists_natCast_of_pow_eq {K : Type*} [Field K] [CharP K q] (a : K) (ha : a ^ q = a) :
    ∃ m : ℕ, (m : K) = a := by
  classical

  set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hP
  have hq1 : 1 < q := hq.out.one_lt
  have hPdeg : P.natDegree = q := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, hq1]
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hPdeg; exact hq.out.ne_zero hPdeg.symm
  have hroot : ∀ b : K, b ^ q = b → b ∈ P.roots := by
    intro b hb
    rw [Polynomial.mem_roots hP0, hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hb, sub_self]

  let ι : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have hι : Function.Injective ι := ι.injective
  let S : Finset K := Finset.univ.image ι
  have hScard : S.card = q := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ZMod.card]
  have hSsub : S ⊆ P.roots.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset]
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hb
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : P.roots.toFinset.card ≤ q := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hPdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hcard)
  have haS : a ∈ S := by rw [hSeq, Multiset.mem_toFinset]; exact hroot a ha
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp haS
  refine ⟨z.val, ?_⟩
  rw [← hz]
  show ((z.val : ℕ) : K) = (z.cast : K)
  rw [ZMod.cast_eq_val]

theorem frobenius_frobenius (x : CerednikDrinfeld.Zp2 q) :
    frobenius (frobenius x) = x := by
  classical
  haveI := Fintype.ofFinite (GaloisField q 2)
  ext n
  rw [coeff_frobenius_charP, coeff_frobenius_charP, ← pow_mul]
  have hc : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  have := FiniteField.pow_card (x.coeff n)
  rwa [hc, pow_two] at this

theorem exists_eq_natCast_add_mul_of_frobenius_eq (x : CerednikDrinfeld.Zp2 q) (hx : frobenius x = x) :
    ∃ (m : ℕ) (c : CerednikDrinfeld.Zp2 q), x = m + (q : CerednikDrinfeld.Zp2 q) * c := by
  have h0 : (x.coeff 0) ^ q = x.coeff 0 := by
    have := congrArg (fun y => WittVector.coeff y 0) hx
    simpa only [coeff_frobenius_charP] using this
  obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q (x.coeff 0) h0
  have hy : (x - m) ∈ Ideal.span {(q : CerednikDrinfeld.Zp2 q)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_natCast, constantCoeff_apply,
      ← hm, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨m, c, by rw [mul_comm, hc]; ring⟩

theorem exists_pow_ne : ∃ ζ : GaloisField q 2, ζ ^ q ≠ ζ := by
  classical
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun m : ZMod q => (m.cast : GaloisField q 2)) := by
    intro a
    obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q a (h a)
    exact ⟨(m : ZMod q), by show ((m : ZMod q).cast : GaloisField q 2) = a; rw [ZMod.cast_natCast (dvd_refl q), hm]⟩
  haveI := Fintype.ofFinite (GaloisField q 2)
  have hle : Fintype.card (GaloisField q 2) ≤ Fintype.card (ZMod q) := Fintype.card_le_of_surjective _ hsurj
  rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card q 2 two_ne_zero, pow_two] at hle
  have hq1 : 1 < q := hq.out.one_lt
  nlinarith

theorem exists_isUnit_sub_frobenius :
    ∃ z : CerednikDrinfeld.Zp2 q, IsUnit (z - frobenius z) := by
  obtain ⟨ζ, hζ⟩ := exists_pow_ne q
  refine ⟨teichmuller q ζ, isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero,
    coeff_frobenius_charP, teichmuller_coeff_zero]
  exact sub_ne_zero.mpr (Ne.symm hζ)

end C1cKit

namespace R3Sol

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries.MvFormalGroup.C1Kit CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

section TypeSplit

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

private abbrev _root_.R3Sol.TA (a : Zp2 q) (h : MvPowerSeries (Fin 2) k) : MvPowerSeries (Fin 2) k := subst (X₀.act a) h

p2m_export "R3Sol" "TA"

def MI (f g : MvPowerSeries (Fin 2) k) : Prop := f - g ∈ I X₀

theorem MI.of_eq {f g : MvPowerSeries (Fin 2) k} (h : f = g) : MI X₀ f g := by
  rw [MI, h, sub_self]; exact Ideal.zero_mem _
theorem MI.rfl' {f : MvPowerSeries (Fin 2) k} : MI X₀ f f := MI.of_eq X₀ rfl
theorem MI.symm {f g : MvPowerSeries (Fin 2) k} (h : MI X₀ f g) : MI X₀ g f := by
  rw [MI] at h ⊢; rw [show g - f = -(f - g) by ring]; exact neg_mem_iff.mpr h
theorem MI.trans {f g h : MvPowerSeries (Fin 2) k} (h1 : MI X₀ f g) (h2 : MI X₀ g h) : MI X₀ f h := by
  rw [MI] at h1 h2 ⊢; rw [show f - h = (f - g) + (g - h) by ring]; exact Ideal.add_mem _ h1 h2
theorem MI.add {f g f' g' : MvPowerSeries (Fin 2) k} (h1 : MI X₀ f g) (h2 : MI X₀ f' g') : MI X₀ (f + f') (g + g') := by
  rw [MI] at h1 h2 ⊢; rw [show f + f' - (g + g') = (f - g) + (f' - g') by ring]; exact Ideal.add_mem _ h1 h2
theorem MI.smul {f g : MvPowerSeries (Fin 2) k} (c : k) (h1 : MI X₀ f g) : MI X₀ (c • f) (c • g) := by
  rw [MI] at h1 ⊢; rw [← smul_sub]; exact smul_mem_ideal' _ c h1
theorem MI.mem_iff {f : MvPowerSeries (Fin 2) k} : MI X₀ f 0 ↔ f ∈ I X₀ := by rw [MI, sub_zero]

theorem hasSubst_act (a : Zp2 q) : HasSubst (X₀.act a) := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)

theorem TA_add (a : Zp2 q) (f g : MvPowerSeries (Fin 2) k) : TA X₀ a (f + g) = TA X₀ a f + TA X₀ a g := by
  show subst (X₀.act a) (f + g) = subst (X₀.act a) f + subst (X₀.act a) g
  rw [← coe_substAlgHom (hasSubst_act X₀ a), map_add]
theorem TA_sub (a : Zp2 q) (f g : MvPowerSeries (Fin 2) k) : TA X₀ a (f - g) = TA X₀ a f - TA X₀ a g := by
  show subst (X₀.act a) (f - g) = subst (X₀.act a) f - subst (X₀.act a) g
  rw [← coe_substAlgHom (hasSubst_act X₀ a), map_sub]
theorem TA_smul (a : Zp2 q) (c : k) (f : MvPowerSeries (Fin 2) k) : TA X₀ a (c • f) = c • TA X₀ a f := by
  show subst (X₀.act a) (c • f) = c • subst (X₀.act a) f
  rw [← coe_substAlgHom (hasSubst_act X₀ a), map_smul]
theorem TA_zero (a : Zp2 q) : TA X₀ a 0 = 0 := by
  show subst (X₀.act a) 0 = 0
  rw [← coe_substAlgHom (hasSubst_act X₀ a), map_zero]

theorem TA_mul (a b : Zp2 q) (h : MvPowerSeries (Fin 2) k) : TA X₀ (a * b) h = TA X₀ b (TA X₀ a h) := by
  show subst (X₀.act (a * b)) h = subst (X₀.act b) (subst (X₀.act a) h)
  rw [X₀.act_mul, subst_comp_subst_apply (hasSubst_act X₀ a) (hasSubst_act X₀ b)]
  rfl

theorem MI.TA (a : Zp2 q) {f g : MvPowerSeries (Fin 2) k} (h : MI X₀ f g) : MI X₀ (TA X₀ a f) (TA X₀ a g) := by
  rw [MI] at h ⊢; rw [← TA_sub]; exact CommQ.subst_mem X₀ (commQ_act X₀ a) h

theorem Prim.add {f g : MvPowerSeries (Fin 2) k} (hf : Prim X₀ f) (hg : Prim X₀ g) : Prim X₀ (f + g) := by
  refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
  have : X₀.F.addCoboundary (f + g) = X₀.F.addCoboundary f + X₀.F.addCoboundary g := by
    rw [addCoboundary, addCoboundary, addCoboundary, ← coe_substAlgHom X₀.F.hasSubst_toPowerSeries,
      ← coe_substAlgHom hasSubst_XL, ← coe_substAlgHom hasSubst_XR, map_add, map_add, map_add]; ring
  rw [this]; exact Ideal.add_mem _ hf.2 hg.2

theorem addCoboundary_smul' (c : k) (f : MvPowerSeries (Fin 2) k) :
    X₀.F.addCoboundary (c • f) = c • X₀.F.addCoboundary f := by
  rw [addCoboundary, addCoboundary, ← coe_substAlgHom X₀.F.hasSubst_toPowerSeries,
    ← coe_substAlgHom hasSubst_XL, ← coe_substAlgHom hasSubst_XR, map_smul, map_smul, map_smul, smul_sub, smul_sub]

theorem Prim.smul (c : k) {f : MvPowerSeries (Fin 2) k} (hf : Prim X₀ f) : Prim X₀ (c • f) := by
  refine ⟨?_, ?_⟩
  · rw [smul_eq_C_mul, map_mul, hf.1, mul_zero]
  · rw [addCoboundary_smul']; exact smul_mem_ideal' _ c hf.2

theorem Prim.sub {f g : MvPowerSeries (Fin 2) k} (hf : Prim X₀ f) (hg : Prim X₀ g) : Prim X₀ (f - g) := by
  rw [sub_eq_add_neg, ← neg_one_smul k g]; exact Prim.add X₀ hf (Prim.smul X₀ _ hg)

theorem Prim.TA (a : Zp2 q) {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) : Prim X₀ (TA X₀ a h) := by
  refine ⟨constantCoeff_subst_eq_zero (hasSubst_act X₀ a) (constantCoeff_act X₀ a) hh.1, ?_⟩
  have hφ := constantCoeff_act X₀ a
  have hP : HasSubst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) :=
    hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  show X₀.F.addCoboundary (subst (X₀.act a) h) ∈ I₂ X₀
  rw [← pull_addCoboundary X₀.F hφ (X₀.isLawHom_act a).2 h]
  refine subst_mem_of_mem_span _ hP _ _ (fun s => ?_) hh.2

  have hgen : ∀ (l : Fin 2),
      subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst (X₀.act a) (X₀.F.nthSeries q l)) ∈ I₂ X₀ ∧
      subst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst (X₀.act a) (X₀.F.nthSeries q l)) ∈ I₂ X₀ := by
    intro l
    have hm : subst (X₀.act a) (X₀.F.nthSeries q l) ∈ I X₀ :=
      CommQ.subst_mem X₀ (commQ_act X₀ a) (Ideal.subset_span ⟨l, rfl⟩)
    constructor
    · exact subst_mem_of_mem_span _ hasSubst_XL _ _ (fun i => Ideal.subset_span (Set.mem_range_self (Sum.inl i))) hm
    · exact subst_mem_of_mem_span _ hasSubst_XR _ _ (fun i => Ideal.subset_span (Set.mem_range_self (Sum.inr i))) hm
  rcases s with l | l
  · show subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) (subst (XL (k := k)) (X₀.F.nthSeries q l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hasSubst_XL hP,
      show (fun t => subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) (XL (k := k) t)) = inL (X₀.act a) from
        funext fun t => subst_X hP _,
      show subst (inL (X₀.act a)) (X₀.F.nthSeries q l) =
        subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst (X₀.act a) (X₀.F.nthSeries q l)) from
        by rw [subst_comp_subst_apply (hasSubst_act X₀ a) hasSubst_XL]]
    exact (hgen l).1
  · show subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) (subst (XR (k := k)) (X₀.F.nthSeries q l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hasSubst_XR hP,
      show (fun t => subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) (XR (k := k) t)) = inR (X₀.act a) from
        funext fun t => subst_X hP _,
      show subst (inR (X₀.act a)) (X₀.F.nthSeries q l) =
        subst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst (X₀.act a) (X₀.F.nthSeries q l)) from
        by rw [subst_comp_subst_apply (hasSubst_act X₀ a) hasSubst_XR]]
    exact (hgen l).2

theorem MI_TA_add {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) (a b : Zp2 q) :
    MI X₀ (TA X₀ (a + b) h) (TA X₀ a h + TA X₀ b h) := by
  show subst (X₀.act (a + b)) h - (subst (X₀.act a) h + subst (X₀.act b) h) ∈ I X₀
  rw [X₀.act_add]
  exact subst_addVia_sub_mem X₀ hh (commQ_act X₀ a) (commQ_act X₀ b)

theorem TA_one (h : MvPowerSeries (Fin 2) k) : TA X₀ 1 h = h := by
  show subst (X₀.act 1) h = h
  rw [X₀.act_one]
  exact congrFun subst_self h

theorem MI_TA_zero {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) : MI X₀ (TA X₀ 0 h) 0 := by
  have h1 := MI_TA_add X₀ hh 0 0
  rw [add_zero] at h1
  rw [MI] at h1 ⊢
  rw [sub_zero]
  have : TA X₀ 0 h - (TA X₀ 0 h + TA X₀ 0 h) = -(TA X₀ 0 h) := by ring
  rw [this] at h1
  exact neg_mem_iff.mp h1

theorem MI_TA_natCast {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) : ∀ n : ℕ, MI X₀ (TA X₀ (n : Zp2 q) h) ((n : k) • h)
  | 0 => by rw [Nat.cast_zero, Nat.cast_zero, zero_smul]; exact MI_TA_zero X₀ hh
  | n + 1 => by
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul]
    exact (MI_TA_add X₀ hh _ _).trans X₀ ((MI_TA_natCast hh n).add X₀ (MI.of_eq X₀ (TA_one X₀ h)))

theorem MI_TA_char {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) : MI X₀ (TA X₀ (q : Zp2 q) h) 0 := by
  rw [MI.mem_iff]
  show subst (X₀.act (q : Zp2 q)) h ∈ I X₀
  rw [X₀.act_natCast]
  exact subst_mem_span _ (constantCoeff_nth X₀) _ hh.1

theorem MI_TA_char_mul {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) (c : Zp2 q) :
    MI X₀ (TA X₀ ((q : Zp2 q) * c) h) 0 := by
  rw [TA_mul]
  have := (MI_TA_char X₀ hh).TA X₀ c
  rwa [TA_zero] at this

theorem MI_TA_of_frobenius_eq {h : MvPowerSeries (Fin 2) k} (hh : Prim X₀ h) {x : Zp2 q}
    (hx : WittVector.frobenius x = x) : MI X₀ (TA X₀ x h) (j₀ x • h) := by
  obtain ⟨m, c, hxe⟩ := C1cKit.exists_eq_natCast_add_mul_of_frobenius_eq q x hx
  have hj : j₀ x = (m : k) := by
    rw [hxe, map_add, map_natCast, map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, add_zero]
  rw [hj, hxe]
  have := (MI_TA_add X₀ hh (m : Zp2 q) ((q : Zp2 q) * c)).trans X₀ ((MI_TA_natCast X₀ hh m).add X₀ (MI_TA_char_mul X₀ hh c))
  rwa [add_zero] at this

theorem exists_decomp' (z : Zp2 q) (hz : IsUnit (z - WittVector.frobenius z)) (a : Zp2 q) :
    ∃ c₀ c₁ : Zp2 q, WittVector.frobenius c₀ = c₀ ∧ WittVector.frobenius c₁ = c₁ ∧ a = c₀ + c₁ * z := by
  obtain ⟨d, hd⟩ := hz
  set σ := (WittVector.frobenius : Zp2 q →+* Zp2 q) with hσ
  have hσσ : ∀ y : Zp2 q, σ (σ y) = y := C1cKit.frobenius_frobenius q
  have hσd : σ (d : Zp2 q) = -(d : Zp2 q) := by rw [hd, map_sub, hσσ]; ring
  have hσdi : σ (↑d⁻¹ : Zp2 q) = -(↑d⁻¹ : Zp2 q) := by
    have h1 : σ (↑d⁻¹ : Zp2 q) * σ (d : Zp2 q) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    rw [hσd] at h1
    calc σ (↑d⁻¹ : Zp2 q) = σ (↑d⁻¹ : Zp2 q) * (-(d : Zp2 q)) * (-(↑d⁻¹ : Zp2 q)) := by
          rw [mul_assoc, neg_mul_neg, Units.mul_inv, mul_one]
      _ = -(↑d⁻¹ : Zp2 q) := by rw [h1, one_mul]
  refine ⟨(z * σ a - a * σ z) * ↑d⁻¹, (a - σ a) * ↑d⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_sub, map_mul, map_mul, hσσ, hσσ, hσdi]; ring
  · rw [map_mul, map_sub, hσσ, hσdi]; ring
  · have hdd : (z - σ z) * ↑d⁻¹ = 1 := by rw [← hd, Units.mul_inv]
    linear_combination (-a) * hdd

theorem MI_eigen {Δ : MvPowerSeries (Fin 2) k} (z : Zp2 q) (α β e : k)
    (hT : MI X₀ (TA X₀ z (TA X₀ z Δ)) ((α + β) • TA X₀ z Δ + (-(α * β)) • Δ)) :
    MI X₀ (TA X₀ z (e • TA X₀ z Δ + (-(β * e)) • Δ)) (α • (e • TA X₀ z Δ + (-(β * e)) • Δ)) := by
  rw [TA_add, TA_smul, TA_smul]
  have h := (hT.smul X₀ e).add X₀ (MI.rfl' X₀ (f := (-(β * e)) • TA X₀ z Δ))
  refine h.trans X₀ (MI.of_eq X₀ ?_)
  module

end TypeSplit

end R3Sol

end

open R3Sol MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries.MvFormalGroup CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (h : MvPowerSeries (Fin 2) k) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hh : X₀.F.addCoboundary h ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))))) :
    ∃ h₀ h₁ : MvPowerSeries (Fin 2) k,
      MvPowerSeries.constantCoeff h₀ = 0 ∧ MvPowerSeries.constantCoeff h₁ = 0 ∧
      X₀.F.addCoboundary h₀ ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      X₀.F.addCoboundary h₁ ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      h - (h₀ + h₁) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
      (∀ a : Zp2 q,
        MvPowerSeries.subst (X₀.act a) h₀ - j₀ a • h₀ ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (X₀.act a) h₁ - j₀ (WittVector.frobenius a) • h₁ ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) := by
  classical
  have hprim : Prim X₀ h := ⟨hh0, hh⟩
  obtain ⟨z, hz⟩ := C1cKit.exists_isUnit_sub_frobenius q
  set σ := (WittVector.frobenius : Zp2 q →+* Zp2 q) with hσ
  have hσσ : ∀ y : Zp2 q, σ (σ y) = y := C1cKit.frobenius_frobenius q
  set α : k := j₀ z with hα
  set β : k := j₀ (σ z) with hβ
  have hαβ : α - β ≠ 0 := by
    rw [hα, hβ, ← map_sub]
    exact (hz.map j₀).ne_zero
  set e : k := (α - β)⁻¹ with he
  have hee : (α - β) * e = 1 := mul_inv_cancel₀ hαβ

  have hs : σ (z + σ z) = z + σ z := by rw [map_add, hσσ, add_comm]
  have ht : σ (z * σ z) = z * σ z := by rw [map_mul, hσσ, mul_comm]
  have hzz : z * z + z * σ z = (z + σ z) * z := by ring
  have hquad : ∀ {Δ : MvPowerSeries (Fin 2) k}, Prim X₀ Δ →
      MI X₀ (TA X₀ z (TA X₀ z Δ)) ((α + β) • TA X₀ z Δ + (-(α * β)) • Δ) := by
    intro Δ hΔ
    have l1 : MI X₀ (TA X₀ (z * z + z * σ z) Δ) (TA X₀ z (TA X₀ z Δ) + (α * β) • Δ) := by
      refine (MI_TA_add X₀ hΔ _ _).trans X₀ ?_
      rw [TA_mul]
      refine ((MI.rfl' X₀).add X₀ (MI_TA_of_frobenius_eq X₀ hΔ ht)).trans X₀ (MI.of_eq X₀ ?_)
      rw [map_mul, ← hα, ← hβ]
    have l2 : MI X₀ (TA X₀ ((z + σ z) * z) Δ) ((α + β) • TA X₀ z Δ) := by
      rw [TA_mul]
      refine ((MI_TA_of_frobenius_eq X₀ hΔ hs).TA X₀ z).trans X₀ (MI.of_eq X₀ ?_)
      rw [TA_smul, map_add, ← hα, ← hβ]
    rw [hzz] at l1
    have l3 := (l1.symm X₀).trans X₀ l2
    have l4 := l3.add X₀ (MI.rfl' X₀ (f := (-(α * β)) • Δ))
    refine (MI.of_eq X₀ ?_).trans X₀ l4
    module

  set T := TA X₀ z with hTdef
  set h₀ : MvPowerSeries (Fin 2) k := e • T h + (-(β * e)) • h with hh₀
  set h₁ : MvPowerSeries (Fin 2) k := (-e) • T h + (α * e) • h with hh₁
  have hTh : Prim X₀ (T h) := Prim.TA X₀ z hprim
  have hp₀ : Prim X₀ h₀ := Prim.add X₀ (Prim.smul X₀ e hTh) (Prim.smul X₀ _ hprim)
  have hp₁ : Prim X₀ h₁ := Prim.add X₀ (Prim.smul X₀ _ hTh) (Prim.smul X₀ _ hprim)
  have hE₀ : MI X₀ (T h₀) (α • h₀) := MI_eigen X₀ z α β e (hquad hprim)
  have hE₁ : MI X₀ (T h₁) (β • h₁) := by
    have hq' : MI X₀ (TA X₀ z (TA X₀ z h)) ((β + α) • TA X₀ z h + (-(β * α)) • h) := by
      rw [add_comm β α, mul_comm β α]; exact hquad hprim
    have := MI_eigen X₀ z β α (-e) hq'
    have h1 : -(α * -e) = α * e := by ring
    rwa [h1] at this

  have key : ∀ (Δ : MvPowerSeries (Fin 2) k) (γ : k), Prim X₀ Δ → MI X₀ (T Δ) (γ • Δ) →
      ∀ a c₀ c₁ : Zp2 q, σ c₀ = c₀ → σ c₁ = c₁ → a = c₀ + c₁ * z →
        MI X₀ (TA X₀ a Δ) ((j₀ c₀ + j₀ c₁ * γ) • Δ) := by
    intro Δ γ hΔ hTΔ a c₀ c₁ hc₀ hc₁ hae
    rw [hae, add_smul]
    refine (MI_TA_add X₀ hΔ _ _).trans X₀ ((MI_TA_of_frobenius_eq X₀ hΔ hc₀).add X₀ ?_)
    rw [TA_mul, mul_smul]
    refine ((MI_TA_of_frobenius_eq X₀ hΔ hc₁).TA X₀ z).trans X₀ ?_
    rw [TA_smul]
    exact hTΔ.smul X₀ _
  refine ⟨h₀, h₁, hp₀.1, hp₁.1, hp₀.2, hp₁.2, ?_, fun a => ⟨?_, ?_⟩⟩
  ·
    have : h₀ + h₁ = h := by
      rw [hh₀, hh₁]
      have : e • T h + -(β * e) • h + (-e • T h + (α * e) • h) = ((α - β) * e) • h := by module
      rw [this, hee, one_smul]
    rw [this, sub_self]; exact Ideal.zero_mem _
  · obtain ⟨c₀, c₁, hc₀, hc₁, hae⟩ := exists_decomp' z hz a
    have := key h₀ α hp₀ hE₀ a c₀ c₁ hc₀ hc₁ hae
    have hj : j₀ c₀ + j₀ c₁ * α = j₀ a := by rw [hae, map_add, map_mul, ← hα]
    rw [hj] at this
    exact this
  · obtain ⟨c₀, c₁, hc₀, hc₁, hae⟩ := exists_decomp' z hz a
    have := key h₁ β hp₁ hE₁ a c₀ c₁ hc₀ hc₁ hae
    have hj : j₀ c₀ + j₀ c₁ * β = j₀ (WittVector.frobenius a) := by
      rw [hae, map_add, map_mul, map_add, map_mul]
      show j₀ c₀ + j₀ c₁ * j₀ (σ z) = j₀ (σ c₀) + j₀ (σ c₁) * j₀ (σ z)
      rw [hc₀, hc₁]
    rw [hj] at this
    exact this

end
end S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries (solution)
