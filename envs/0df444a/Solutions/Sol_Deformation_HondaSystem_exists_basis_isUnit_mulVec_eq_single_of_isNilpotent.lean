-- Prove2me | solution 1 for Deformation.HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/57fedb51-1b6e-5c78-ab44-1287662e43d7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent

set_option autoImplicit false

universe u v w

namespace Deformation
namespace HondaSystem
namespace NormalFormC12

open Module

section Flag

variable {k : Type w} [Field k]

private theorem restrict_pow_apply {V : Type v} [AddCommGroup V] [Module k V] (f : V →ₗ[k] V)
    (W : Submodule k V) (hW : ∀ x ∈ W, f x ∈ W) :
    ∀ (N : ℕ) (x : W), ((f.restrict hW ^ N) x : V) = (f ^ N) (x : V) := by
  intro N
  induction N with
  | zero => intro x; simp
  | succ N ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, LinearMap.coe_restrict_apply]

private theorem exists_basis_triangular :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (f : V →ₗ[k] V),
      IsNilpotent f → finrank k V = n →
      ∃ w : Fin n → V, LinearIndependent k w ∧ Submodule.span k (Set.range w) = ⊤ ∧
        ∀ i : Fin n, f (w i) ∈ Submodule.span k (w '' {j | i < j}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hf hn
    classical
    obtain ⟨N, hN⟩ := hf
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    ·
      subst hn0
      haveI : Subsingleton V := Module.finrank_zero_iff.1 hn
      refine ⟨Fin.elim0, linearIndependent_empty_type, ?_, fun i => Fin.elim0 i⟩
      exact Submodule.eq_top_iff'.2 fun x => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _

    set W : Submodule k V := LinearMap.range f with hWdef
    have hWlt : W < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => ?_
      have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
      have hinj : Function.Injective f := LinearMap.injective_iff_surjective.2 hsurj
      have hinjN : Function.Injective (f ^ N) := by
        rw [Module.End.coe_pow]; exact hinj.iterate N
      haveI : Subsingleton V := ⟨fun a b => hinjN (by rw [hN]; rfl)⟩
      have : finrank k V = 0 := Module.finrank_zero_of_subsingleton
      omega
    have hWstab : ∀ x ∈ W, f x ∈ W := fun x _ => LinearMap.mem_range_self f x
    set m := finrank k W with hmdef
    have hm : m < n := by rw [← hn, ← finrank_top k V]; exact Submodule.finrank_lt_finrank_of_lt hWlt

    have hfW : IsNilpotent (f.restrict hWstab) := ⟨N, by
      ext x
      have h := restrict_pow_apply f W hWstab N x
      rw [hN, LinearMap.zero_apply] at h
      rw [LinearMap.zero_apply, ZeroMemClass.coe_zero]
      exact h⟩
    obtain ⟨wt, hwt_li, hwt_span, hwt_tri⟩ := ih m hm W (f.restrict hWstab) hfW rfl

    obtain ⟨Wc, hc⟩ := Submodule.exists_isCompl W
    set c := finrank k Wc with hcdef
    have hcm : c + m = n := by rw [hcdef, hmdef, Submodule.finrank_add_eq_of_isCompl hc.symm, hn]
    let bc := Module.finBasis k Wc
    let u : Fin c → V := fun i => (bc i : V)
    let wv : Fin m → V := fun i => (wt i : V)
    have hu_li : LinearIndependent k u := bc.linearIndependent.map' Wc.subtype (Submodule.ker_subtype _)
    have hwv_li : LinearIndependent k wv := hwt_li.map' W.subtype (Submodule.ker_subtype _)
    have hu_span : Submodule.span k (Set.range u) = Wc := by
      show Submodule.span k (Set.range (⇑Wc.subtype ∘ ⇑bc)) = Wc
      rw [Set.range_comp, Submodule.span_image, bc.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hwv_span : Submodule.span k (Set.range wv) = W := by
      show Submodule.span k (Set.range (⇑W.subtype ∘ wt)) = W
      rw [Set.range_comp, Submodule.span_image, hwt_span, Submodule.map_top, Submodule.range_subtype]
    have hz_li : LinearIndependent k (Sum.elim u wv) := by
      refine hu_li.sum_type hwv_li ?_
      rw [hu_span, hwv_span]
      exact hc.symm.disjoint

    let σ : Fin c ⊕ Fin m ≃ Fin n := finSumFinEquiv.trans (finCongr hcm)
    let z : Fin n → V := Sum.elim u wv ∘ σ.symm
    have hzσ : ∀ s, z (σ s) = Sum.elim u wv s := fun s => by
      show Sum.elim u wv (σ.symm (σ s)) = _; rw [Equiv.symm_apply_apply]
    have hσval_l : ∀ a : Fin c, ((σ (Sum.inl a) : Fin n) : ℕ) = a := fun a => by
      simp [σ, finSumFinEquiv_apply_left]
    have hσval_r : ∀ b : Fin m, ((σ (Sum.inr b) : Fin n) : ℕ) = c + b := fun b => by
      simp [σ, finSumFinEquiv_apply_right]
    refine ⟨z, (linearIndependent_equiv σ.symm).2 hz_li, ?_, ?_⟩
    ·
      have hrange : Set.range z = Set.range (Sum.elim u wv) := σ.symm.surjective.range_comp _
      rw [hrange, Set.Sum.elim_range, Submodule.span_union, hu_span, hwv_span]
      exact hc.symm.sup_eq_top
    ·
      intro i

      have himage : ∀ (b : Fin m), (i : ℕ) < c + b → wv b ∈ z '' {j | i < j} := by
        intro b hb
        refine ⟨σ (Sum.inr b), ?_, hzσ _⟩
        show i < σ (Sum.inr b)
        rw [Fin.lt_def, hσval_r]
        exact hb
      obtain ⟨s, rfl⟩ := σ.surjective i
      rw [hzσ]
      rcases s with a | b
      ·
        have hmem : f (u a) ∈ W := LinearMap.mem_range_self f _
        rw [← hwv_span] at hmem
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨b, rfl⟩
        exact himage b (by rw [hσval_l]; omega)
      ·
        have h := hwt_tri b
        have h' : f (wv b) ∈ Submodule.map W.subtype (Submodule.span k (wt '' {b' | b < b'})) := by
          refine ⟨f.restrict hWstab (wt b), h, ?_⟩
          rw [LinearMap.restrict_apply]; rfl
        rw [← Submodule.span_image, ← Set.image_comp] at h'
        refine Submodule.span_mono ?_ h'
        rintro _ ⟨b', hb', rfl⟩
        exact himage b' (by rw [hσval_r]; exact Nat.add_lt_add_left hb' c)

end Flag

section Lift

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hjac : Ideal.span {(p : 𝓞)} ≤ (⊥ : Ideal 𝓞).jacobson)

include hker hjac in

private theorem isUnit_of_isUnit_map {d : ℕ} (P : Matrix (Fin d) (Fin d) 𝓞)
    (hP : IsUnit (P.map (algebraMap 𝓞 (ZMod p)))) : IsUnit P := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det] at hP ⊢
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hP
  obtain ⟨b, hb⟩ := hP.exists_right_inv
  obtain ⟨b, rfl⟩ := ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p)) b
  rw [← map_mul, ← map_one (algebraMap 𝓞 (ZMod p)), ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker] at hb
  exact isUnit_of_mul_isUnit_left (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hjac hb))

end Lift

end Deformation.HondaSystem.NormalFormC12

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (L : Type v) [AddCommGroup L] [Module 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (hrank : Module.finrank 𝓞 L = d)
    (lam₀ lam₁ : L →ₗ[𝓞] (Fin d → ZMod p)) (hsurj : Function.Surjective lam₀)
    (hkerlam : ∀ m : L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 L))
    (C : Matrix (Fin d) (Fin d) (ZMod p)) (hC : IsNilpotent C) (hlam₁ : ∀ m, lam₁ m = C.mulVec (lam₀ m)) :
    ∃ (b : Module.Basis (Fin d) 𝓞 L) (P : Matrix (Fin d) (Fin d) 𝓞), IsUnit P ∧
      (∀ i, (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₀ (b i)) = Pi.single i 1) ∧
      (∀ i j : Fin d, j ≤ i → (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₁ (b i)) j = 0) := by
  classical
  have hpp : p.Prime := Fact.out
  have hjac : Ideal.span {(p : 𝓞)} ≤ (⊥ : Ideal 𝓞).jacobson := IsAdicComplete.le_jacobson_bot _
  have hsurjO : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  have hfnil : IsNilpotent (Matrix.toLin' C) := by
    obtain ⟨N, hN⟩ := hC
    exact ⟨N, by rw [← Matrix.toLin'_pow, hN, map_zero]⟩
  obtain ⟨w, hw_li, hw_span, hw_tri⟩ :=
    Deformation.HondaSystem.NormalFormC12.exists_basis_triangular (k := ZMod p) d (Fin d → ZMod p)
      (Matrix.toLin' C) hfnil (Module.finrank_fin_fun (ZMod p))

  set Wm : Matrix (Fin d) (Fin d) (ZMod p) := Matrix.of fun l i => w i l with hWm
  have hWcol : ∀ i, Wm.col i = w i := fun i => funext fun l => rfl
  have hWunit : IsUnit Wm := by
    have hcols : Wm.col = w := funext hWcol
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcols]
    exact hw_li
  have hWdet : IsUnit Wm.det := (Matrix.isUnit_iff_isUnit_det _).1 hWunit
  set Pb : Matrix (Fin d) (Fin d) (ZMod p) := Wm⁻¹ with hPb
  have hPbW : Pb * Wm = 1 := Matrix.nonsing_inv_mul _ hWdet
  have hWPb : Wm * Pb = 1 := Matrix.mul_nonsing_inv _ hWdet
  have hPbw : ∀ i, Pb.mulVec (w i) = Pi.single i 1 := by
    intro i
    rw [← hWcol, ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hPbW, Matrix.one_mulVec]

  choose lift hlift using hsurjO
  let P : Matrix (Fin d) (Fin d) 𝓞 := Pb.map lift
  have hPmap : P.map (algebraMap 𝓞 (ZMod p)) = Pb := by
    ext i j; simp only [P, Matrix.map_apply, hlift]
  have hPbunit : IsUnit Pb := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hWdet)
  have hPunit : IsUnit P :=
    Deformation.HondaSystem.NormalFormC12.isUnit_of_isUnit_map p hker hjac P (by rw [hPmap]; exact hPbunit)

  choose bv hbv using fun i => hsurj (w i)
  have hspan : (⊤ : Submodule 𝓞 L) ≤ Submodule.span 𝓞 (Set.range bv) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun m _ => ?_

    set cb : Fin d → ZMod p := Pb.mulVec (lam₀ m) with hcb
    have hdecomp : lam₀ m = ∑ i, cb i • w i := by
      have h1 : Wm.mulVec cb = lam₀ m := by
        rw [hcb, Matrix.mulVec_mulVec, hWPb, Matrix.one_mulVec]
      rw [← h1]
      funext l
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hWm, Matrix.of_apply,
        mul_comm]
    let cc : Fin d → 𝓞 := fun i => lift (cb i)
    have hrest : m - ∑ i, cc i • bv i ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 L) := by
      refine hkerlam _ ?_
      rw [map_sub, map_sum, hdecomp, sub_eq_zero]
      refine (Finset.sum_congr rfl fun i _ => ?_).symm
      rw [map_smul, hbv, ← algebraMap_smul (ZMod p) (cc i) (w i), hlift]
    rw [show m = (∑ i, cc i • bv i) + (m - ∑ i, cc i • bv i) by abel]
    exact Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))) hrest
  have hli : LinearIndependent 𝓞 bv :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, hrank])
  refine ⟨Module.Basis.mk hli hspan, P, hPunit, fun i => ?_, fun i j hji => ?_⟩
  · rw [Module.Basis.mk_apply, hPmap, hbv, hPbw]
  · rw [Module.Basis.mk_apply, hPmap, hlam₁, hbv]
    have h := hw_tri i
    rw [Matrix.toLin'_apply] at h
    obtain ⟨t, ht, cfun, hsum⟩ := (Submodule.mem_span_image_iff_exists_fun (ZMod p)).1 h
    rw [← hsum, ← Matrix.mulVecLin_apply, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply, hPbw, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : i < (x : Fin d) := ht x.2
    rw [if_neg (ne_of_lt (lt_of_le_of_lt hji hx)), mul_zero]

end S_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent (solution)
