-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e4874693-8009-5e2b-986c-d0bf94c57a6b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two
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

namespace R3wSol

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

end Assembly

section Devissage

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

abbrev J : Ideal (MvPowerSeries (Fin 2) k) := Ideal.span (Set.range X₀.varpi)

abbrev J₂ : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) k) := Ideal.span (Set.range (vv X₀))

def PrimJ (h : MvPowerSeries (Fin 2) k) : Prop := constantCoeff h = 0 ∧ X₀.F.addCoboundary h ∈ J₂ X₀
def HasTypeJ (χ : Zp2 q → k) (g : MvPowerSeries (Fin 2) k) : Prop := ∀ a, subst (X₀.act a) g - χ a • g ∈ J X₀

theorem nth_eq_subst_varpi (i : Fin 2) : X₀.F.nthSeries q i = subst X₀.varpi (X₀.varpi i) := by
  have h := X₀.varpi_comp_varpi
  rw [FormalODModule.act_natCast] at h
  exact (congrFun h i).symm

theorem I_le_J : I X₀ ≤ J X₀ := by
  rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
  rw [nth_eq_subst_varpi]
  exact subst_mem_span _ (constantCoeff_varpi X₀) _ (constantCoeff_varpi X₀ i)

theorem I₂_le_J₂ : I₂ X₀ ≤ J₂ X₀ := by
  have hXL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsvv : HasSubst (vv X₀) := hasSubst_of_constantCoeff_zero (vv_const X₀)
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  rw [Ideal.span_le]; rintro _ ⟨s, rfl⟩
  rcases s with i | i
  · show subst XL (X₀.F.nthSeries q i) ∈ J₂ X₀
    rw [nth_eq_subst_varpi, subst_comp_subst_apply hsϖ hXL]
    refine Ideal.span_mono ?_ (subst_mem_span (fun j => subst (XL (k := k)) (X₀.varpi j)) (fun j => vv_const X₀ (Sum.inl j)) _ (constantCoeff_varpi X₀ i))
    rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j, rfl⟩
  · show subst XR (X₀.F.nthSeries q i) ∈ J₂ X₀
    rw [nth_eq_subst_varpi, subst_comp_subst_apply hsϖ hXR]
    refine Ideal.span_mono ?_ (subst_mem_span (fun j => subst (XR (k := k)) (X₀.varpi j)) (fun j => vv_const X₀ (Sum.inr j)) _ (constantCoeff_varpi X₀ i))
    rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩

theorem prim_to_primJ {g : MvPowerSeries (Fin 2) k} (hg : Prim X₀ g) : PrimJ X₀ g := ⟨hg.1, I₂_le_J₂ X₀ hg.2⟩
theorem type_to_typeJ {χ : Zp2 q → k} {g : MvPowerSeries (Fin 2) k} (hg : HasType X₀ χ g) : HasTypeJ X₀ χ g :=
  fun a => I_le_J X₀ (hg a)

theorem subst_varpi_mem_I {f : MvPowerSeries (Fin 2) k} (hf : f ∈ J X₀) : subst X₀.varpi f ∈ I X₀ := by
  refine subst_mem_of_mem_span _ (hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)) X₀.varpi (I X₀) (fun i => ?_) hf
  rw [← nth_eq_subst_varpi]; exact Ideal.subset_span ⟨i, rfl⟩

theorem subst_act_mem_J (a : Zp2 q) {f : MvPowerSeries (Fin 2) k} (hf : f ∈ J X₀) : subst (X₀.act a) f ∈ J X₀ := by
  refine subst_mem_of_mem_span _ (hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)) X₀.varpi (J X₀) (fun i => ?_) hf
  have h := congrFun (X₀.varpi_comp_act a) i
  show subst (X₀.act a) (X₀.varpi i) ∈ J X₀
  change (X₀.varpi.comp (X₀.act a)) i ∈ J X₀
  rw [h]
  exact subst_mem_span _ (constantCoeff_varpi X₀) _ (constantCoeff_act X₀ _ i)

theorem addCoboundary_subst (u : Series k) (hu0 : ∀ i, constantCoeff (u i) = 0)
    (hu : ∀ j, subst X₀.F.toPowerSeries (u j) =
      subst (Sum.elim (fun l => subst (XL (k := k)) (u l)) (fun l => subst (XR (k := k)) (u l))) (X₀.F.toPowerSeries j))
    (g : MvPowerSeries (Fin 2) k) :
    X₀.F.addCoboundary (subst u g) =
      subst (Sum.elim (fun l => subst (XL (k := k)) (u l)) (fun l => subst (XR (k := k)) (u l))) (X₀.F.addCoboundary g) := by
  have hsu := hasSubst_of_constantCoeff_zero hu0
  have hXL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have huu0 : ∀ s, constantCoeff (Sum.elim (fun l => subst (XL (k := k)) (u l)) (fun l => subst (XR (k := k)) (u l)) s) = 0 := by
    rintro (l | l)
    · exact constantCoeff_subst_eq_zero hXL (fun _ => constantCoeff_X _) (hu0 l)
    · exact constantCoeff_subst_eq_zero hXR (fun _ => constantCoeff_X _) (hu0 l)
  have hsuu : HasSubst (Sum.elim (fun l => subst (XL (k := k)) (u l)) (fun l => subst (XR (k := k)) (u l))) :=
    hasSubst_of_constantCoeff_zero huu0
  set uu := (Sum.elim (fun l => subst (XL (k := k)) (u l)) (fun l => subst (XR (k := k)) (u l))) with huu
  have hF : subst X₀.F.toPowerSeries (subst u g) = subst uu (subst X₀.F.toPowerSeries g) := by
    rw [subst_comp_subst_apply hsu X₀.F.hasSubst_toPowerSeries, subst_comp_subst_apply X₀.F.hasSubst_toPowerSeries hsuu]
    congr 1; funext j; rw [hu j]
  have hL : subst (XL (k := k)) (subst u g) = subst uu (subst (XL (k := k)) g) := by
    rw [subst_comp_subst_apply hsu hXL, subst_comp_subst_apply hXL hsuu]
    congr 1; funext j; exact (subst_X hsuu (Sum.inl j)).symm
  have hR : subst (XR (k := k)) (subst u g) = subst uu (subst (XR (k := k)) g) := by
    rw [subst_comp_subst_apply hsu hXR, subst_comp_subst_apply hXR hsuu]
    congr 1; funext j; exact (subst_X hsuu (Sum.inr j)).symm
  rw [MvFormalGroup.addCoboundary, MvFormalGroup.addCoboundary, hF, hL, hR, ← coe_substAlgHom hsuu, map_sub, map_sub]

theorem primJ_subst_act (a : Zp2 q) {h : MvPowerSeries (Fin 2) k} (hh : PrimJ X₀ h) : PrimJ X₀ (subst (X₀.act a) h) := by
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  have hXL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨constantCoeff_subst_eq_zero hsa (constantCoeff_act X₀ a) hh.1, ?_⟩
  rw [addCoboundary_subst X₀ (X₀.act a) (constantCoeff_act X₀ a) (X₀.isLawHom_act a).2]
  set aa := (Sum.elim (fun l => subst (XL (k := k)) (X₀.act a l)) (fun l => subst (XR (k := k)) (X₀.act a l))) with haa
  have haa0 : ∀ s, constantCoeff (aa s) = 0 := by
    rintro (l | l)
    · exact constantCoeff_subst_eq_zero hXL (fun _ => constantCoeff_X _) (constantCoeff_act X₀ a l)
    · exact constantCoeff_subst_eq_zero hXR (fun _ => constantCoeff_X _) (constantCoeff_act X₀ a l)
  have hsaa : HasSubst aa := hasSubst_of_constantCoeff_zero haa0
  refine subst_mem_of_mem_span _ hsaa _ (J₂ X₀) (fun s => ?_) hh.2
  rcases s with l | l
  · show subst aa (subst XL (X₀.varpi l)) ∈ J₂ X₀
    rw [subst_comp_subst_apply hXL hsaa, show (fun t => subst aa (XL (k := k) t)) = fun j => subst XL (X₀.act a j)
      from funext fun t => subst_X hsaa (Sum.inl t), ← subst_comp_subst_apply hsa hXL]
    refine subst_mem_of_mem_span _ hXL X₀.varpi (J₂ X₀) (fun i => Ideal.subset_span ⟨Sum.inl i, rfl⟩) (subst_act_mem_J X₀ a (Ideal.subset_span ⟨l, rfl⟩))
  · show subst aa (subst XR (X₀.varpi l)) ∈ J₂ X₀
    rw [subst_comp_subst_apply hXR hsaa, show (fun t => subst aa (XR (k := k) t)) = fun j => subst XR (X₀.act a j)
      from funext fun t => subst_X hsaa (Sum.inr t), ← subst_comp_subst_apply hsa hXR]
    refine subst_mem_of_mem_span _ hXR X₀.varpi (J₂ X₀) (fun i => Ideal.subset_span ⟨Sum.inr i, rfl⟩) (subst_act_mem_J X₀ a (Ideal.subset_span ⟨l, rfl⟩))

theorem primJ_subst_varpi {h : MvPowerSeries (Fin 2) k} (hh : PrimJ X₀ h) : Prim X₀ (subst X₀.varpi h) := by
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hsvv : HasSubst (vv X₀) := hasSubst_of_constantCoeff_zero (vv_const X₀)
  have hXL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨constantCoeff_subst_eq_zero hsϖ (constantCoeff_varpi X₀) hh.1, ?_⟩
  rw [addCoboundary_subst X₀ X₀.varpi (constantCoeff_varpi X₀) X₀.isLawHom_varpi.2]
  refine subst_mem_of_mem_span _ hsvv _ (I₂ X₀) (fun s => ?_) hh.2
  rcases s with l | l
  · show subst (vv X₀) (subst XL (X₀.varpi l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hXL hsvv, show (fun t => subst (vv X₀) (XL (k := k) t)) = fun j => subst XL (X₀.varpi j)
      from funext fun t => subst_X hsvv (Sum.inl t), ← subst_comp_subst_apply hsϖ hXL, ← nth_eq_subst_varpi]
    exact Ideal.subset_span ⟨Sum.inl l, rfl⟩
  · show subst (vv X₀) (subst XR (X₀.varpi l)) ∈ I₂ X₀
    rw [subst_comp_subst_apply hXR hsvv, show (fun t => subst (vv X₀) (XR (k := k) t)) = fun j => subst XR (X₀.varpi j)
      from funext fun t => subst_X hsvv (Sum.inr t), ← subst_comp_subst_apply hsϖ hXR, ← nth_eq_subst_varpi]
    exact Ideal.subset_span ⟨Sum.inr l, rfl⟩

theorem typeJ_subst_varpi {χ : Zp2 q → k} {h : MvPowerSeries (Fin 2) k} (hh : HasTypeJ X₀ χ h) :
    HasType X₀ (fun a => χ (WittVector.frobenius a)) (subst X₀.varpi h) := by
  intro a
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  have hsa' := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ (WittVector.frobenius a))
  have e : subst (X₀.act a) (subst X₀.varpi h) = subst X₀.varpi (subst (X₀.act (WittVector.frobenius a)) h) := by
    rw [subst_comp_subst_apply hsϖ hsa, subst_comp_subst_apply hsa' hsϖ]
    congr 1; exact X₀.varpi_comp_act a
  rw [e, ← subst_smul hsϖ, ← subst_sub hsϖ]
  exact subst_varpi_mem_I X₀ (hh _)

theorem primJ_smul (c : k) {h} (hh : PrimJ X₀ h) : PrimJ X₀ (c • h) := by
  refine ⟨by rw [smul_eq_C_mul, map_mul, hh.1, mul_zero], ?_⟩
  have : X₀.F.addCoboundary (c • h) = c • X₀.F.addCoboundary h := by
    simp only [MvFormalGroup.addCoboundary, subst_smul X₀.F.hasSubst_toPowerSeries,
      subst_smul (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), smul_sub]
  rw [this]; exact smul_mem_ideal' _ c hh.2

theorem primJ_sub {h h'} (hh : PrimJ X₀ h) (hh' : PrimJ X₀ h') : PrimJ X₀ (h - h') := by
  refine ⟨by rw [map_sub, hh.1, hh'.1, sub_zero], ?_⟩
  have : X₀.F.addCoboundary (h - h') = X₀.F.addCoboundary h - X₀.F.addCoboundary h' := by
    simp only [MvFormalGroup.addCoboundary, subst_sub X₀.F.hasSubst_toPowerSeries,
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    ring
  rw [this]; exact Ideal.sub_mem _ hh.2 hh'.2

theorem prim_smul (c : k) {h} (hh : Prim X₀ h) : Prim X₀ (c • h) := by
  refine ⟨by rw [smul_eq_C_mul, map_mul, hh.1, mul_zero], ?_⟩
  have : X₀.F.addCoboundary (c • h) = c • X₀.F.addCoboundary h := by
    simp only [MvFormalGroup.addCoboundary, subst_smul X₀.F.hasSubst_toPowerSeries,
      subst_smul (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), smul_sub]
  rw [this]; exact smul_mem_ideal' _ c hh.2

theorem prim_add {h h'} (hh : Prim X₀ h) (hh' : Prim X₀ h') : Prim X₀ (h + h') := by
  refine ⟨by rw [map_add, hh.1, hh'.1, add_zero], ?_⟩
  have : X₀.F.addCoboundary (h + h') = X₀.F.addCoboundary h + X₀.F.addCoboundary h' := by
    simp only [MvFormalGroup.addCoboundary, subst_add X₀.F.hasSubst_toPowerSeries,
      subst_add (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    ring
  rw [this]; exact Ideal.add_mem _ hh.2 hh'.2

theorem hasType_smul {χ : Zp2 q → k} (c : k) {g} (hg : HasType X₀ χ g) : HasType X₀ χ (c • g) := fun a => by
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  rw [subst_smul hsa, smul_comm, ← smul_sub]; exact smul_mem_I X₀ c (hg a)

theorem hasType_add {χ : Zp2 q → k} {g g'} (hg : HasType X₀ χ g) (hg' : HasType X₀ χ g') : HasType X₀ χ (g + g') := fun a => by
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  rw [subst_add hsa, smul_add, show ∀ x y z w : MvPowerSeries (Fin 2) k, x + y - (z + w) = (x - z) + (y - w) from fun _ _ _ _ => by ring]
  exact Ideal.add_mem _ (hg a) (hg' a)

theorem hasType_of_sub_mem {χ : Zp2 q → k} {g g'} (hg : HasType X₀ χ g) (h : g' - g ∈ I X₀) : HasType X₀ χ g' := fun a => by
  have hsa := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)
  have e : subst (X₀.act a) g' - χ a • g' = (subst (X₀.act a) g - χ a • g) + (subst (X₀.act a) (g' - g) - χ a • (g' - g)) := by
    rw [subst_sub hsa, smul_sub]; ring
  rw [e]; exact Ideal.add_mem _ (hg a) (Ideal.sub_mem _ (CommQ.subst_mem X₀ (commQ_act X₀ a) h) (smul_mem_I X₀ _ h))

end Devissage

section MainAssembly

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

theorem sigma_sigma (a : Zp2 q) : WittVector.frobenius (WittVector.frobenius a) = a :=
  TChar.C1cKit.frobenius_frobenius q a

theorem mem_I_of_two_types {g : MvPowerSeries (Fin 2) k} (h₀ : HasType X₀ j₀ g)
    (h₁ : HasType X₀ (fun a => j₀ (WittVector.frobenius a)) g) : g ∈ I X₀ := by
  obtain ⟨z, hz⟩ := TChar.C1cKit.exists_isUnit_sub_frobenius q
  set d : k := j₀ z - j₀ (WittVector.frobenius z) with hd
  have hd0 : d ≠ 0 := by rw [hd, ← map_sub]; exact (hz.map j₀).ne_zero
  have hmem : d • g ∈ I X₀ := by
    have e : d • g = (subst (X₀.act z) g - j₀ (WittVector.frobenius z) • g) - (subst (X₀.act z) g - j₀ z • g) := by
      rw [hd, sub_smul]; abel
    rw [e]; exact Ideal.sub_mem _ (h₁ z) (h₀ z)
  have : g = d⁻¹ • (d • g) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  rw [this]; exact smul_mem_I X₀ _ hmem

theorem desc_typed {ψ : Zp2 q → k} {g : MvPowerSeries (Fin 2) k} (hg : Prim X₀ g) (hT : HasType X₀ ψ g)
    (hJ : g ∈ J X₀) :
    ∃ h, PrimJ X₀ h ∧ HasTypeJ X₀ (fun a => ψ (WittVector.frobenius a)) h ∧ g - subst X₀.varpi h ∈ I X₀ := by
  obtain ⟨h, h0, hP, hgI⟩ :=
    (CerednikDrinfeld.SpecialFormalODModule.mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi X₀).2
      g hg.1 hg.2 hJ
  have hh : PrimJ X₀ h := ⟨h0, hP⟩
  refine ⟨h, hh, fun b => ?_, hgI⟩

  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have hw : PrimJ X₀ (subst (X₀.act b) h - ψ (WittVector.frobenius b) • h) :=
    primJ_sub X₀ (primJ_subst_act X₀ b hh) (primJ_smul X₀ _ hh)
  have hgT' : HasType X₀ ψ (subst X₀.varpi h) := hasType_of_sub_mem X₀ hT (by
    have : subst X₀.varpi h - g = -(g - subst X₀.varpi h) := by ring
    rw [this]; exact (I X₀).neg_mem hgI)
  have key : subst X₀.varpi (subst (X₀.act b) h - ψ (WittVector.frobenius b) • h) ∈ I X₀ := by
    have hsb := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ b)
    have hsb' := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ (WittVector.frobenius b))
    have e : subst X₀.varpi (subst (X₀.act b) h) = subst (X₀.act (WittVector.frobenius b)) (subst X₀.varpi h) := by
      rw [subst_comp_subst_apply hsb hsϖ, subst_comp_subst_apply hsϖ hsb']
      congr 1
      have := X₀.varpi_comp_act (WittVector.frobenius b)
      rw [sigma_sigma] at this
      exact this.symm
    rw [subst_sub hsϖ, subst_smul hsϖ, e]
    exact hgT' (WittVector.frobenius b)
  exact (CerednikDrinfeld.SpecialFormalODModule.mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi X₀).1
    _ hw.1 hw.2 key

theorem dep_of_mem_J {ψ : Zp2 q → k} {g g' : MvPowerSeries (Fin 2) k} (hg : Prim X₀ g) (hg' : Prim X₀ g')
    (hT : HasType X₀ ψ g) (hT' : HasType X₀ ψ g') (hJ : g ∈ J X₀) (hJ' : g' ∈ J X₀) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ I X₀ := by
  obtain ⟨h, hh, hhT, hgh⟩ := desc_typed X₀ hg hT hJ
  obtain ⟨h', hh', hhT', hgh'⟩ := desc_typed X₀ hg' hT' hJ'
  obtain ⟨c, c', hcc, hmem⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem X₀ _ h h'
      hh.1 hh'.1 hh.2 hh'.2 hhT hhT'
  refine ⟨c, c', hcc, ?_⟩
  have hsϖ := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  have h1 := subst_varpi_mem_I X₀ hmem
  rw [subst_add hsϖ, subst_smul hsϖ, subst_smul hsϖ] at h1
  have e : c • g + c' • g' = (c • subst X₀.varpi h + c' • subst X₀.varpi h') + (c • (g - subst X₀.varpi h) + c' • (g' - subst X₀.varpi h')) := by
    simp only [smul_sub]; abel
  rw [e]; exact Ideal.add_mem _ h1 (Ideal.add_mem _ (smul_mem_I X₀ _ hgh) (smul_mem_I X₀ _ hgh'))

theorem exists_twisted_of_not_mem_J {ψ : Zp2 q → k} {h : MvPowerSeries (Fin 2) k} (hh : PrimJ X₀ h)
    (hT : HasTypeJ X₀ ψ h) (hnJ : h ∉ J X₀) :
    Prim X₀ (subst X₀.varpi h) ∧ HasType X₀ (fun a => ψ (WittVector.frobenius a)) (subst X₀.varpi h) ∧
      subst X₀.varpi h ∈ J X₀ ∧ subst X₀.varpi h ∉ I X₀ := by
  refine ⟨primJ_subst_varpi X₀ hh, typeJ_subst_varpi X₀ hT,
    subst_mem_span _ (constantCoeff_varpi X₀) _ hh.1, fun hI => hnJ ?_⟩
  exact (CerednikDrinfeld.SpecialFormalODModule.mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi X₀).1
    _ hh.1 hh.2 hI

theorem exists_not_mem_of_type (ψ : Zp2 q → k) (ψ' : Zp2 q → k)
    (hψ' : ∀ a, ψ' a = ψ (WittVector.frobenius a)) (hψ : ∀ a, ψ a = ψ' (WittVector.frobenius a))
    (e e' : MvPowerSeries (Fin 2) k) (he : Prim X₀ e) (he' : Prim X₀ e')
    (hind : ∀ c c' : k, c • e + c' • e' ∈ I X₀ → c = 0 ∧ c' = 0)
    (hsplit : ∀ g, Prim X₀ g → ∃ g₀ g₁, Prim X₀ g₀ ∧ Prim X₀ g₁ ∧ g - (g₀ + g₁) ∈ I X₀ ∧ HasType X₀ ψ g₀ ∧ HasType X₀ ψ' g₁) :
    ∃ g, Prim X₀ g ∧ HasType X₀ ψ' g ∧ g ∉ I X₀ := by
  by_contra hnone
  push_neg at hnone

  have hiJ : ∀ h, PrimJ X₀ h → HasTypeJ X₀ ψ h → h ∈ J X₀ := by
    intro h hh hT
    by_contra hnJ
    obtain ⟨hP, hT', -, hnI⟩ := exists_twisted_of_not_mem_J X₀ hh hT hnJ
    exact hnI (hnone _ hP (fun a => by rw [hψ' a]; exact hT' a))

  have hii : ∀ g, Prim X₀ g → HasType X₀ ψ g → g ∈ J X₀ := fun g hg hT =>
    hiJ g (prim_to_primJ X₀ hg) (type_to_typeJ X₀ hT)

  obtain ⟨e₀, e₁, he₀, he₁, hes, hT₀, hT₁⟩ := hsplit e he
  obtain ⟨e₀', e₁', he₀', he₁', hes', hT₀', hT₁'⟩ := hsplit e' he'
  have h1 : e₁ ∈ I X₀ := hnone _ he₁ hT₁
  have h1' : e₁' ∈ I X₀ := hnone _ he₁' hT₁'
  obtain ⟨c, c', hcc, hdep⟩ := dep_of_mem_J X₀ he₀ he₀' hT₀ hT₀' (hii _ he₀ hT₀) (hii _ he₀' hT₀')
  have hmem : c • e + c' • e' ∈ I X₀ := by
    have eq : c • e + c' • e' = (c • e₀ + c' • e₀') + (c • (e - (e₀ + e₁)) + c' • (e' - (e₀' + e₁'))) + (c • e₁ + c' • e₁') := by
      simp only [smul_sub, smul_add]; abel
    rw [eq]
    exact Ideal.add_mem _ (Ideal.add_mem _ hdep (Ideal.add_mem _ (smul_mem_I X₀ _ hes) (smul_mem_I X₀ _ hes')))
      (Ideal.add_mem _ (smul_mem_I X₀ _ h1) (smul_mem_I X₀ _ h1'))
  obtain ⟨hc, hc'⟩ := hind c c' hmem
  rcases hcc with h | h <;> contradiction

theorem span_of_indep {e e' g₀ g₁ : MvPowerSeries (Fin 2) k}
    (hspan : ∀ g, Prim X₀ g → ∃ a b : k, g - (a • e + b • e') ∈ I X₀)
    (hg₀ : Prim X₀ g₀) (hg₁ : Prim X₀ g₁)
    (hind : ∀ c c' : k, c • g₀ + c' • g₁ ∈ I X₀ → c = 0 ∧ c' = 0)
    (g : MvPowerSeries (Fin 2) k) (hg : Prim X₀ g) :
    ∃ c c' : k, g - (c • g₀ + c' • g₁) ∈ I X₀ := by
  obtain ⟨α, β, r₀⟩ := hspan g₀ hg₀
  obtain ⟨γ, δ, r₁⟩ := hspan g₁ hg₁
  obtain ⟨a, b, rg⟩ := hspan g hg
  set D : k := α * δ - β * γ with hD
  have hD0 : D ≠ 0 := by
    intro hD0

    have m1 : δ • g₀ + (-β) • g₁ ∈ I X₀ := by
      have eq : δ • g₀ + (-β) • g₁ = δ • (g₀ - (α • e + β • e')) + (-β) • (g₁ - (γ • e + δ • e')) + D • e := by
        rw [hD]; simp only [smul_sub, smul_add, smul_smul, sub_smul]; module
      rw [eq, hD0, zero_smul, add_zero]
      exact Ideal.add_mem _ (smul_mem_I X₀ _ r₀) (smul_mem_I X₀ _ r₁)
    have m2 : (-γ) • g₀ + α • g₁ ∈ I X₀ := by
      have eq : (-γ) • g₀ + α • g₁ = (-γ) • (g₀ - (α • e + β • e')) + α • (g₁ - (γ • e + δ • e')) + D • e' := by
        rw [hD]; simp only [smul_sub, smul_add, smul_smul, sub_smul]; module
      rw [eq, hD0, zero_smul, add_zero]
      exact Ideal.add_mem _ (smul_mem_I X₀ _ r₀) (smul_mem_I X₀ _ r₁)
    obtain ⟨hδ, hβ⟩ := hind _ _ m1
    obtain ⟨hγ, hα⟩ := hind _ _ m2
    have hα0 : α = 0 := hα
    have hγ0 : γ = 0 := by simpa using hγ

    have m3 : (1 : k) • g₀ + (0 : k) • g₁ ∈ I X₀ := by
      rw [one_smul, zero_smul, add_zero]
      have : g₀ = (g₀ - (α • e + β • e')) := by rw [hα0, show β = 0 from by simpa using hβ]; simp
      rw [this]; exact r₀
    exact one_ne_zero (hind 1 0 m3).1
  refine ⟨D⁻¹ * (a * δ - b * γ), D⁻¹ * (b * α - a * β), ?_⟩
  have key : D • g - ((a * δ - b * γ) • g₀ + (b * α - a * β) • g₁) =
      D • (g - (a • e + b • e')) - (a * δ) • (g₀ - (α • e + β • e')) + (a * β) • (g₁ - (γ • e + δ • e'))
        + (b * γ) • (g₀ - (α • e + β • e')) - (b * α) • (g₁ - (γ • e + δ • e')) := by
    rw [hD]; simp only [smul_sub, smul_add, smul_smul, sub_smul]; module
  have hmem : D • g - ((a * δ - b * γ) • g₀ + (b * α - a * β) • g₁) ∈ I X₀ := by
    rw [key]
    refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.sub_mem _ (smul_mem_I X₀ _ rg) (smul_mem_I X₀ _ r₀))
      (smul_mem_I X₀ _ r₁)) (smul_mem_I X₀ _ r₀)) (smul_mem_I X₀ _ r₁)
  have e2 : g - ((D⁻¹ * (a * δ - b * γ)) • g₀ + (D⁻¹ * (b * α - a * β)) • g₁) =
      D⁻¹ • (D • g - ((a * δ - b * γ) • g₀ + (b * α - a * β) • g₁)) := by
    rw [smul_sub, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [e2]; exact smul_mem_I X₀ _ hmem

end MainAssembly

section Final

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

theorem hasType_sub_smul {χ : Zp2 q → k} {h g : MvPowerSeries (Fin 2) k} (hh : HasType X₀ χ h) (hg : HasType X₀ χ g) (c : k) :
    HasType X₀ χ (h - c • g) := by
  have : h - c • g = h + (-c) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [this]; exact hasType_add X₀ hh (hasType_smul X₀ _ hg)

theorem main
    (hdim : ∃ e e' : MvPowerSeries (Fin 2) k,
      constantCoeff e = 0 ∧ constantCoeff e' = 0 ∧
      X₀.F.addCoboundary e ∈ I₂ X₀ ∧ X₀.F.addCoboundary e' ∈ I₂ X₀ ∧
      (∀ c c' : k, c • e + c' • e' ∈ I X₀ → c = 0 ∧ c' = 0) ∧
      (∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 → X₀.F.addCoboundary g ∈ I₂ X₀ →
        ∃ c c' : k, g - (c • e + c' • e') ∈ I X₀)) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k,
      (∀ i, constantCoeff (g i) = 0) ∧
      (∀ i, X₀.F.addCoboundary (g i) ∈ I₂ X₀) ∧
      (∀ i, g i ∉ I X₀) ∧
      (∀ a : Zp2 q,
        subst (X₀.act a) (g 0) - j₀ a • g 0 ∈ I X₀ ∧
        subst (X₀.act a) (g 1) - j₀ (WittVector.frobenius a) • g 1 ∈ I X₀) ∧
      (∀ h : MvPowerSeries (Fin 2) k, constantCoeff h = 0 → X₀.F.addCoboundary h ∈ I₂ X₀ →
        ((∀ a : Zp2 q, subst (X₀.act a) h - j₀ a • h ∈ I X₀) → ∃ c : k, h - c • g 0 ∈ I X₀) ∧
        ((∀ a : Zp2 q, subst (X₀.act a) h - j₀ (WittVector.frobenius a) • h ∈ I X₀) → ∃ c : k, h - c • g 1 ∈ I X₀)) := by
  obtain ⟨e, e', he0, he'0, heP, he'P, hind, hspan⟩ := hdim
  have he : Prim X₀ e := ⟨he0, heP⟩
  have he' : Prim X₀ e' := ⟨he'0, he'P⟩
  have hspan' : ∀ g, Prim X₀ g → ∃ a b : k, g - (a • e + b • e') ∈ I X₀ := fun g hg => hspan g hg.1 hg.2

  have hsplit : ∀ g, Prim X₀ g → ∃ g₀ g₁, Prim X₀ g₀ ∧ Prim X₀ g₁ ∧ g - (g₀ + g₁) ∈ I X₀ ∧
      HasType X₀ j₀ g₀ ∧ HasType X₀ (fun a => j₀ (WittVector.frobenius a)) g₁ := by
    intro g hg
    obtain ⟨g₀, g₁, h00, h10, h0P, h1P, hs, hT⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_add_typed_of_primitive_mod_nthSeries X₀ g hg.1 hg.2
    exact ⟨g₀, g₁, ⟨h00, h0P⟩, ⟨h10, h1P⟩, hs, fun a => (hT a).1, fun a => (hT a).2⟩
  have hsplit' : ∀ g, Prim X₀ g → ∃ g₀ g₁, Prim X₀ g₀ ∧ Prim X₀ g₁ ∧ g - (g₀ + g₁) ∈ I X₀ ∧
      HasType X₀ (fun a => j₀ (WittVector.frobenius a)) g₀ ∧ HasType X₀ j₀ g₁ := by
    intro g hg
    obtain ⟨g₀, g₁, hg₀, hg₁, hs, hT₀, hT₁⟩ := hsplit g hg
    exact ⟨g₁, g₀, hg₁, hg₀, by rwa [add_comm], hT₁, hT₀⟩

  obtain ⟨g₁, hg₁, hT1, hn1⟩ := exists_not_mem_of_type X₀ j₀ (fun a => j₀ (WittVector.frobenius a))
    (fun a => rfl) (fun a => by show j₀ a = j₀ (WittVector.frobenius (WittVector.frobenius a)); rw [sigma_sigma])
    e e' he he' hind hsplit
  obtain ⟨g₀, hg₀, hT0, hn0⟩ := exists_not_mem_of_type X₀ (fun a => j₀ (WittVector.frobenius a)) j₀
    (fun a => by show j₀ a = j₀ (WittVector.frobenius (WittVector.frobenius a)); rw [sigma_sigma]) (fun a => rfl)
    e e' he he' hind hsplit'
  have hind' := indep_of_types X₀ hT0 hT1 hn0 hn1
  refine ⟨![g₀, g₁], ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i; exacts [hg₀.1, hg₁.1]
  · intro i; fin_cases i; exacts [hg₀.2, hg₁.2]
  · intro i; fin_cases i; exacts [hn0, hn1]
  · intro a; exact ⟨hT0 a, hT1 a⟩
  · intro h hh0 hhP
    have hh : Prim X₀ h := ⟨hh0, hhP⟩
    obtain ⟨c, c', hcc⟩ := span_of_indep X₀ hspan' hg₀ hg₁ (fun c c' hm => hind' c c' hm) h hh
    constructor
    · intro hTh
      refine ⟨c, ?_⟩

      have hy : HasType X₀ j₀ (c' • g₁) := by
        refine hasType_of_sub_mem X₀ (hasType_sub_smul X₀ hTh hT0 c) ?_
        have : c' • g₁ - (h - c • g₀) = -(h - (c • g₀ + c' • g₁)) := by abel
        rw [this]; exact (I X₀).neg_mem hcc
      have hyI := mem_I_of_two_types X₀ hy (hasType_smul X₀ c' hT1)
      have : h - c • (![g₀, g₁] : Fin 2 → _) 0 = (h - (c • g₀ + c' • g₁)) + c' • g₁ := by
        simp only [Matrix.cons_val_zero]; abel
      rw [this]; exact Ideal.add_mem _ hcc hyI
    · intro hTh
      refine ⟨c', ?_⟩
      have hy : HasType X₀ (fun a => j₀ (WittVector.frobenius a)) (c • g₀) := by
        refine hasType_of_sub_mem X₀ (hasType_sub_smul X₀ hTh hT1 c') ?_
        have : c • g₀ - (h - c' • g₁) = -(h - (c • g₀ + c' • g₁)) := by abel
        rw [this]; exact (I X₀).neg_mem hcc
      have hyI := mem_I_of_two_types X₀ (hasType_smul X₀ c hT0) hy
      have : h - c' • (![g₀, g₁] : Fin 2 → _) 1 = (h - (c • g₀ + c' • g₁)) + c • g₀ := by
        simp only [Matrix.cons_val_one, Matrix.head_cons]; abel
      rw [this]; exact Ideal.add_mem _ hcc hyI

end Final

end R3wSol

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
      (∀ i, g i ∉ Ideal.span (Set.range (X₀.F.nthSeries q))) ∧
      (∀ a : Zp2 q,
        MvPowerSeries.subst (X₀.act a) (g 0) - j₀ a • g 0 ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (X₀.act a) (g 1) - j₀ (WittVector.frobenius a) • g 1 ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) ∧
      (∀ h : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff h = 0 →
        X₀.F.addCoboundary h ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) →
        ((∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) h - j₀ a • h ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) →
            ∃ c : k, h - c • g 0 ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) ∧
        ((∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) h - j₀ (WittVector.frobenius a) • h ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) →
            ∃ c : k, h - c • g 1 ∈ Ideal.span (Set.range (X₀.F.nthSeries q)))) :=
  R3wSol.main X₀ hdim

end S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two (solution)
