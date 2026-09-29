-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a6306d95-3959-58b2-b5b3-ca118a18d6bc

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace TChar

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

end TChar

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

section Assembly

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

def HasType (χ : Zp2 q → k) (g : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ a, subst (X₀.act a) g - χ a • g ∈ I X₀

theorem subst_XL_mem_I₂ {f : MvPowerSeries (Fin 2) k} (hf : f ∈ I X₀) : subst (XL (k := k)) f ∈ I₂ X₀ :=
  subst_mem_of_mem_span _ (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) (X₀.F.nthSeries q) (I₂ X₀)
    (fun i => Ideal.subset_span ⟨Sum.inl i, rfl⟩) hf

theorem subst_XR_mem_I₂ {f : MvPowerSeries (Fin 2) k} (hf : f ∈ I X₀) : subst (XR (k := k)) f ∈ I₂ X₀ :=
  subst_mem_of_mem_span _ (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _) (X₀.F.nthSeries q) (I₂ X₀)
    (fun i => Ideal.subset_span ⟨Sum.inr i, rfl⟩) hf

abbrev vv : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  Sum.elim (fun j => subst (XL (k := k)) (X₀.varpi j)) (fun j => subst (XR (k := k)) (X₀.varpi j))

theorem vv_const (s : Fin 2 ⊕ Fin 2) : constantCoeff (vv X₀ s) = 0 := by
  rcases s with j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _)
      (fun t => constantCoeff_X _) (constantCoeff_varpi X₀ j)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _)
      (fun t => constantCoeff_X _) (constantCoeff_varpi X₀ j)

theorem prim_subst_varpi {g : MvPowerSeries (Fin 2) k} (hg : Prim X₀ g) : Prim X₀ (subst X₀.varpi g) := by
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hsvv : HasSubst (vv X₀) := hasSubst_of_constantCoeff_zero (vv_const X₀)
  have hXL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _
  have hXR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun t => constantCoeff_X _
  refine ⟨constantCoeff_subst_eq_zero hsϖ (constantCoeff_varpi X₀) hg.1, ?_⟩
  have hF : subst X₀.F.toPowerSeries (subst X₀.varpi g) = subst (vv X₀) (subst X₀.F.toPowerSeries g) := by
    rw [subst_comp_subst_apply hsϖ X₀.F.hasSubst_toPowerSeries, subst_comp_subst_apply X₀.F.hasSubst_toPowerSeries hsvv]
    congr 1; funext j
    exact X₀.isLawHom_varpi.2 j
  have hL : subst (XL (k := k)) (subst X₀.varpi g) = subst (vv X₀) (subst (XL (k := k)) g) := by
    rw [subst_comp_subst_apply hsϖ hXL, subst_comp_subst_apply hXL hsvv]
    congr 1; funext j; exact (subst_X hsvv (Sum.inl j)).symm
  have hR : subst (XR (k := k)) (subst X₀.varpi g) = subst (vv X₀) (subst (XR (k := k)) g) := by
    rw [subst_comp_subst_apply hsϖ hXR, subst_comp_subst_apply hXR hsvv]
    congr 1; funext j; exact (subst_X hsvv (Sum.inr j)).symm
  have e : X₀.F.addCoboundary (subst X₀.varpi g) = subst (vv X₀) (X₀.F.addCoboundary g) := by
    rw [MvFormalGroup.addCoboundary, MvFormalGroup.addCoboundary, hF, hL, hR, ← coe_substAlgHom hsvv, map_sub, map_sub]
  rw [e]
  refine subst_mem_of_mem_span _ hsvv _ _ (fun s => ?_) hg.2
  rcases s with l | l
  · show subst (vv X₀) (subst XL (X₀.F.nthSeries q l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hXL hsvv, show (fun t => subst (vv X₀) (XL (k := k) t)) = fun j => subst XL (X₀.varpi j)
      from funext fun t => subst_X hsvv (Sum.inl t), ← subst_comp_subst_apply hsϖ hXL, (commQ_varpi X₀).2 l]
    exact subst_XL_mem_I₂ X₀ (subst_mem_span _ (constantCoeff_nth X₀) _ (constantCoeff_varpi X₀ l))
  · show subst (vv X₀) (subst XR (X₀.F.nthSeries q l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hXR hsvv, show (fun t => subst (vv X₀) (XR (k := k) t)) = fun j => subst XR (X₀.varpi j)
      from funext fun t => subst_X hsvv (Sum.inr t), ← subst_comp_subst_apply hsϖ hXR, (commQ_varpi X₀).2 l]
    exact subst_XR_mem_I₂ X₀ (subst_mem_span _ (constantCoeff_nth X₀) _ (constantCoeff_varpi X₀ l))

theorem hasType_subst_varpi {g : MvPowerSeries (Fin 2) k} {χ : Zp2 q → k} (hχ : HasType X₀ χ g) :
    HasType X₀ (fun a => χ (WittVector.frobenius a)) (subst X₀.varpi g) := by
  intro a
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  have hsa' := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ (WittVector.frobenius a))
  have e : subst (X₀.act a) (subst X₀.varpi g) = subst X₀.varpi (subst (X₀.act (WittVector.frobenius a)) g) := by
    rw [subst_comp_subst_apply hsϖ hsa, subst_comp_subst_apply hsa' hsϖ]
    congr 1
    exact X₀.varpi_comp_act a
  have e2 : subst (X₀.act a) (subst X₀.varpi g) - χ (WittVector.frobenius a) • subst X₀.varpi g =
      subst X₀.varpi (subst (X₀.act (WittVector.frobenius a)) g - χ (WittVector.frobenius a) • g) := by
    rw [subst_sub hsϖ, subst_smul hsϖ, e]
  rw [e2]
  exact CommQ.subst_mem X₀ (commQ_varpi X₀) (hχ _)

theorem subst_act_comp_varpi_sub_mem {g : MvPowerSeries (Fin 2) k} {χ : Zp2 q → k} (hχ : HasType X₀ χ g) (β : Zp2 q) :
    subst ((X₀.act β).comp X₀.varpi) g - χ β • subst X₀.varpi g ∈ I X₀ := by
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hsb := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ β)
  have e : subst ((X₀.act β).comp X₀.varpi) g = subst X₀.varpi (subst (X₀.act β) g) := by
    rw [subst_comp_subst_apply hsb hsϖ]; rfl
  rw [e, ← subst_smul hsϖ, ← subst_sub hsϖ]
  exact CommQ.subst_mem X₀ (commQ_varpi X₀) (hχ β)

theorem smul_mem_I (c : k) {f : MvPowerSeries (Fin 2) k} (hf : f ∈ I X₀) : c • f ∈ I X₀ := smul_mem_ideal' _ c hf

theorem indep_of_types {g₀ g₁ : MvPowerSeries (Fin 2) k} (h₀ : HasType X₀ j₀ g₀)
    (h₁ : HasType X₀ (fun a => j₀ (WittVector.frobenius a)) g₁) (hg₀ : g₀ ∉ I X₀) (hg₁ : g₁ ∉ I X₀)
    (c₀ c₁ : k) (hc : c₀ • g₀ + c₁ • g₁ ∈ I X₀) : c₀ = 0 ∧ c₁ = 0 := by
  obtain ⟨z, hz⟩ := TChar.C1cKit.exists_isUnit_sub_frobenius q
  have hsz := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ z)
  set d : k := j₀ z - j₀ (WittVector.frobenius z) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, ← map_sub]; exact (hz.map j₀).ne_zero

  have h1 : c₀ • (j₀ z • g₀) + c₁ • (j₀ (WittVector.frobenius z) • g₁) ∈ I X₀ := by
    have := CommQ.subst_mem X₀ (commQ_act X₀ z) hc
    rw [← coe_substAlgHom hsz, map_add, map_smul, map_smul, coe_substAlgHom hsz] at this
    have e : c₀ • (j₀ z • g₀) + c₁ • (j₀ (WittVector.frobenius z) • g₁) =
        (c₀ • subst (X₀.act z) g₀ + c₁ • subst (X₀.act z) g₁) -
          (c₀ • (subst (X₀.act z) g₀ - j₀ z • g₀) + c₁ • (subst (X₀.act z) g₁ - j₀ (WittVector.frobenius z) • g₁)) := by
      simp only [smul_sub]; abel
    rw [e]
    exact Ideal.sub_mem _ this (Ideal.add_mem _ (smul_mem_I X₀ _ (h₀ z)) (smul_mem_I X₀ _ (h₁ z)))

  have h2 : (c₀ * d) • g₀ ∈ I X₀ := by
    have e : (c₀ * d) • g₀ = (c₀ • (j₀ z • g₀) + c₁ • (j₀ (WittVector.frobenius z) • g₁)) -
        j₀ (WittVector.frobenius z) • (c₀ • g₀ + c₁ • g₁) := by
      rw [hd]; simp only [smul_add, smul_smul, sub_smul, mul_sub]; module
    rw [e]; exact Ideal.sub_mem _ h1 (smul_mem_I X₀ _ hc)
  have h3 : (c₁ * d) • g₁ ∈ I X₀ := by
    have e : (c₁ * d) • g₁ = j₀ z • (c₀ • g₀ + c₁ • g₁) -
        (c₀ • (j₀ z • g₀) + c₁ • (j₀ (WittVector.frobenius z) • g₁)) := by
      rw [hd]; simp only [smul_add, smul_smul, mul_sub]; module
    rw [e]; exact Ideal.sub_mem _ (smul_mem_I X₀ _ hc) h1
  constructor
  · by_contra hc0
    apply hg₀
    have : g₀ = (c₀ * d)⁻¹ • ((c₀ * d) • g₀) := by rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc0 hd0), one_smul]
    rw [this]; exact smul_mem_I X₀ _ h2
  · by_contra hc1
    apply hg₁
    have : g₁ = (c₁ * d)⁻¹ • ((c₁ * d) • g₁) := by rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc1 hd0), one_smul]
    rw [this]; exact smul_mem_I X₀ _ h3

theorem main (hdim : ∃ e e' : MvPowerSeries (Fin 2) k,
      constantCoeff e = 0 ∧ constantCoeff e' = 0 ∧
      X₀.F.addCoboundary e ∈ I₂ X₀ ∧
      X₀.F.addCoboundary e' ∈ I₂ X₀ ∧
      (∀ c c' : k, c • e + c' • e' ∈ I X₀ → c = 0 ∧ c' = 0) ∧
      (∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 →
        X₀.F.addCoboundary g ∈ I₂ X₀ →
        ∃ c c' : k, g - (c • e + c' • e') ∈ I X₀)) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k,
      (∀ i, constantCoeff (g i) = 0) ∧
      (∀ i, X₀.F.addCoboundary (g i) ∈ I₂ X₀) ∧
      (∀ c : Fin 2 → k, (∑ i, c i • g i) ∈ I X₀ → c = 0) ∧
      (∀ a : Zp2 q,
        subst (X₀.act a) (g 0) - j₀ a • g 0 ∈ I X₀ ∧
        subst (X₀.act a) (g 1) - j₀ (WittVector.frobenius a) • g 1 ∈ I X₀) ∧
      (∀ α β : Zp2 q, ∃ c : Fin 2 → k,
        subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 0)
            - (j₀ α • g 0 + c 0 • g 1) ∈ I X₀ ∧
        subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 1)
            - (j₀ (WittVector.frobenius α) • g 1 + c 1 • g 0) ∈ I X₀) := by
  obtain ⟨g, hg0, hgP, hgI, hgT, hlines⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two X₀ hdim
  have hT0 : HasType X₀ j₀ (g 0) := fun a => (hgT a).1
  have hT1 : HasType X₀ (fun a => j₀ (WittVector.frobenius a)) (g 1) := fun a => (hgT a).2
  refine ⟨g, hg0, hgP, fun c hc => ?_, hgT, fun α β => ?_⟩
  · rw [Fin.sum_univ_two] at hc
    obtain ⟨h0, h1⟩ := indep_of_types X₀ hT0 hT1 (hgI 0) (hgI 1) (c 0) (c 1) hc
    funext i; fin_cases i <;> assumption
  ·
    have hw0 : Prim X₀ (subst X₀.varpi (g 0)) := prim_subst_varpi X₀ ⟨hg0 0, hgP 0⟩
    have hw1 : Prim X₀ (subst X₀.varpi (g 1)) := prim_subst_varpi X₀ ⟨hg0 1, hgP 1⟩
    have hwT0 := hasType_subst_varpi X₀ hT0
    have hwT1 := hasType_subst_varpi X₀ hT1
    have hσσ : ∀ a : Zp2 q, j₀ (WittVector.frobenius (WittVector.frobenius a)) = j₀ a := fun a => by
      rw [TChar.C1cKit.frobenius_frobenius q a]
    obtain ⟨c₀, hc₀⟩ := ((hlines _ hw0.1 hw0.2).2) hwT0
    obtain ⟨c₁, hc₁⟩ := ((hlines _ hw1.1 hw1.2).1) (fun a => by have := hwT1 a; simp only [hσσ] at this; exact this)

    have hu := commQ_act X₀ α
    have hv := CommQ.comp X₀ (commQ_act X₀ β) (commQ_varpi X₀)
    have add0 := subst_addVia_sub_mem X₀ ⟨hg0 0, hgP 0⟩ hu hv
    have add1 := subst_addVia_sub_mem X₀ ⟨hg0 1, hgP 1⟩ hu hv
    have v0 := subst_act_comp_varpi_sub_mem X₀ hT0 β
    have v1 := subst_act_comp_varpi_sub_mem X₀ hT1 β
    refine ⟨![j₀ β * c₀, j₀ (WittVector.frobenius β) * c₁], ?_, ?_⟩
    · have e : subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 0) - (j₀ α • g 0 + (j₀ β * c₀) • g 1) =
          (subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 0)
              - (subst (X₀.act α) (g 0) + subst ((X₀.act β).comp X₀.varpi) (g 0))) +
          (subst (X₀.act α) (g 0) - j₀ α • g 0) +
          (subst ((X₀.act β).comp X₀.varpi) (g 0) - j₀ β • subst X₀.varpi (g 0)) +
          j₀ β • (subst X₀.varpi (g 0) - c₀ • g 1) := by
        simp only [smul_sub, smul_smul]; abel
      simp only [Matrix.cons_val_zero]
      rw [e]
      exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ add0 (hT0 α)) v0) (smul_mem_I X₀ _ hc₀)
    · have e : subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 1)
            - (j₀ (WittVector.frobenius α) • g 1 + (j₀ (WittVector.frobenius β) * c₁) • g 0) =
          (subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 1)
              - (subst (X₀.act α) (g 1) + subst ((X₀.act β).comp X₀.varpi) (g 1))) +
          (subst (X₀.act α) (g 1) - j₀ (WittVector.frobenius α) • g 1) +
          (subst ((X₀.act β).comp X₀.varpi) (g 1) - j₀ (WittVector.frobenius β) • subst X₀.varpi (g 1)) +
          j₀ (WittVector.frobenius β) • (subst X₀.varpi (g 1) - c₁ • g 0) := by
        simp only [smul_sub, smul_smul]; abel
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      rw [e]
      exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ add1 (hT1 α)) v1) (smul_mem_I X₀ _ hc₁)

end Assembly

end R3Sol

end

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hdim : ∃ e e' : MvPowerSeries (Fin 2) k,
      MvPowerSeries.constantCoeff e = 0 ∧ MvPowerSeries.constantCoeff e' = 0 ∧
      X₀.F.addCoboundary e ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      X₀.F.addCoboundary e' ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      (∀ c c' : k, c • e + c' • e' ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) → c = 0 ∧ c' = 0) ∧
      (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) →
        ∃ c c' : k, g - (c • e + c' • e') ∈ Ideal.span (Set.range (X₀.F.nthSeries q)))) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k,
      (∀ i, MvPowerSeries.constantCoeff (g i) = 0) ∧
      (∀ i, X₀.F.addCoboundary (g i) ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))))) ∧
      (∀ c : Fin 2 → k, (∑ i, c i • g i) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) → c = 0) ∧
      (∀ a : Zp2 q,
        MvPowerSeries.subst (X₀.act a) (g 0) - j₀ a • g 0 ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (X₀.act a) (g 1) - j₀ (WittVector.frobenius a) • g 1 ∈
          Ideal.span (Set.range (X₀.F.nthSeries q))) ∧
      (∀ α β : Zp2 q, ∃ c : Fin 2 → k,
        MvPowerSeries.subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 0)
            - (j₀ α • g 0 + c 0 • g 1) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 1)
            - (j₀ (WittVector.frobenius α) • g 1 + c 1 • g 0) ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) :=
  R3Sol.main X₀ hdim

end S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two (solution)
