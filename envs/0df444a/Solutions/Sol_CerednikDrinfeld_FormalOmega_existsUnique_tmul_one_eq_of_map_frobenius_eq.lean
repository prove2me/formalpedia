-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_tmul_one_eq_of_map_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3ff780b4-00f6-5256-8ac2-9f0beaaad788

import Theorems.Thm_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq

set_option autoImplicit false

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.fixedPoints_frobenius_levels"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "fixedPoints_frobenius_levels"
namespace AffineDescentAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

section LevelDescent

variable {R B T : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing T] [Algebra R T]

theorem map_id_autT_tmul (G : T ≃ₐ[R] T) (b : B) (t : T) :
    Algebra.TensorProduct.map (AlgHom.id R B) (G : T →ₐ[R] T) (b ⊗ₜ[R] t) = b ⊗ₜ[R] G t := by
  simp [Algebra.TensorProduct.map_tmul]

theorem map_id_autT_mul (G H : T ≃ₐ[R] T) (v : B ⊗[R] T) :
    Algebra.TensorProduct.map (AlgHom.id R B) ((G * H : T ≃ₐ[R] T) : T →ₐ[R] T) v =
      Algebra.TensorProduct.map (AlgHom.id R B) (G : T →ₐ[R] T)
        (Algebra.TensorProduct.map (AlgHom.id R B) (H : T →ₐ[R] T) v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul b t => simp [AlgEquiv.mul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_id_autT_one (v : B ⊗[R] T) :
    Algebra.TensorProduct.map (AlgHom.id R B) ((1 : T ≃ₐ[R] T) : T →ₐ[R] T) v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul b t => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_id_autT_pow_fixed (G : T ≃ₐ[R] T) (w : B ⊗[R] T)
    (hw : Algebra.TensorProduct.map (AlgHom.id R B) (G : T →ₐ[R] T) w = w) (j : ℕ) :
    Algebra.TensorProduct.map (AlgHom.id R B) ((G ^ j : T ≃ₐ[R] T) : T →ₐ[R] T) w = w := by
  induction j with
  | zero => rw [pow_zero, map_id_autT_one]
  | succ j ih => rw [pow_succ, map_id_autT_mul, hw, ih]

theorem level_descent (k : ℕ) (hk : 0 < k) (ζ : T) (σ : T ≃ₐ[R] T)
    (bT : Module.Basis (Fin k) R T) (hbT : ∀ i, bT i = ζ ^ (i : ℕ))
    (hunit : ∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ))
    (w : B ⊗[R] T) (hw : Algebra.TensorProduct.map (AlgHom.id R B) (σ : T →ₐ[R] T) w = w) :
    ∃ b : B, w = b ⊗ₜ[R] (1 : T) := by
  classical
  set bB := Algebra.TensorProduct.basis B bT with hbB
  set c : Fin k → B := fun i => bB.repr w i with hc
  have hw_exp : w = ∑ i, (c i) ⊗ₜ[R] (ζ ^ (i : ℕ)) := by
    conv_lhs => rw [← bB.sum_repr w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbB, Algebra.TensorProduct.basis_apply, hbT, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hw_j : ∀ j : ℕ, w = ∑ i, (c i) ⊗ₜ[R] (((σ ^ j) ζ) ^ (i : ℕ)) := by
    intro j
    conv_lhs => rw [← map_id_autT_pow_fixed σ w hw j, hw_exp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_id_autT_tmul, map_pow]

  set v : Fin k → B ⊗[R] T := fun j => (1 : B) ⊗ₜ[R] ((σ ^ (j : ℕ)) ζ) with hv
  set V : Matrix (Fin k) (Fin k) (B ⊗[R] T) := Matrix.vandermonde v with hV
  have hdet : IsUnit V.det := by
    rw [hV, Matrix.det_vandermonde]
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
    have hu := (hunit j i hij).map (Algebra.TensorProduct.includeRight : T →ₐ[R] B ⊗[R] T)
    simpa [hv, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_sub] using hu
  have hVunit : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr hdet
  set cC : Fin k → B ⊗[R] T := fun i => (c i) ⊗ₜ[R] (1 : T) with hcC
  set e0 : Fin k → B ⊗[R] T := fun i => if i = (⟨0, hk⟩ : Fin k) then w else 0 with he0
  have hmul1 : V.mulVec cC = fun _ => w := by
    funext j
    rw [hw_j (j : ℕ)]
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hv, hcC,
      Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hmul2 : V.mulVec e0 = fun _ => w := by
    funext j
    simp only [Matrix.mulVec, dotProduct, he0, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hV, Matrix.vandermonde_apply, pow_zero, one_mul]
  obtain ⟨u, hu⟩ := hVunit
  have hcc : cC = e0 := by
    have h1 : V.mulVec cC = V.mulVec e0 := hmul1.trans hmul2.symm
    have h2 := congrArg (fun x => ((u⁻¹ : (Matrix (Fin k) (Fin k) (B ⊗[R] T))ˣ) :
      Matrix (Fin k) (Fin k) (B ⊗[R] T)).mulVec x) h1
    simp only [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  refine ⟨c ⟨0, hk⟩, ?_⟩
  have := congrFun hcc ⟨0, hk⟩
  simp only [hcC, he0, if_true] at this
  exact this.symm

theorem eq_zero_of_tmul_one_eq_zero {ι : Type} (bT : Module.Basis ι R T) (i0 : ι) (hbT0 : bT i0 = 1)
    (b : B) (h : b ⊗ₜ[R] (1 : T) = 0) : b = 0 := by
  have := congrArg (fun x => (Algebra.TensorProduct.basis B bT).repr x i0) h
  rw [← hbT0] at this
  simpa [Algebra.TensorProduct.basis_repr_tmul] using this

end LevelDescent

section Levels

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

abbrev Lev (F : S ≃ₐ[R] S) (k : ℕ) : Subalgebra R S :=
  AlgHom.equalizer ((F ^ k : S ≃ₐ[R] S) : S →ₐ[R] S) (AlgHom.id R S)

theorem mem_Lev {F : S ≃ₐ[R] S} {k : ℕ} {x : S} : x ∈ Lev F k ↔ (F ^ k) x = x := by
  simp [AlgHom.mem_equalizer]

theorem pow_mul_apply_of_fixed (F : S ≃ₐ[R] S) (k l : ℕ) (x : S) (h : (F ^ k) x = x) :
    (F ^ (k * l)) x = x := by
  induction l with
  | zero => simp
  | succ l ih => rw [Nat.mul_succ, pow_add, AlgEquiv.mul_apply, h, ih]

theorem Lev_le_of_dvd (F : S ≃ₐ[R] S) {k K : ℕ} (h : k ∣ K) : Lev F k ≤ Lev F K := by
  obtain ⟨l, rfl⟩ := h
  intro x hx
  exact mem_Lev.mpr (pow_mul_apply_of_fixed F k l x (mem_Lev.mp hx))

variable (B : Type) [CommRing B] [Algebra R B]

abbrev ι (F : S ≃ₐ[R] S) (k : ℕ) : B ⊗[R] Lev F k →ₐ[R] B ⊗[R] S :=
  Algebra.TensorProduct.map (AlgHom.id R B) (Lev F k).val

abbrev incl (F : S ≃ₐ[R] S) {k K : ℕ} (h : k ∣ K) : B ⊗[R] Lev F k →ₐ[R] B ⊗[R] Lev F K :=
  Algebra.TensorProduct.map (AlgHom.id R B) (Subalgebra.inclusion (Lev_le_of_dvd F h))

theorem ι_incl (F : S ≃ₐ[R] S) {k K : ℕ} (h : k ∣ K) (w : B ⊗[R] Lev F k) :
    ι B F K (incl B F h w) = ι B F k w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [Algebra.TensorProduct.map_tmul, Subalgebra.coe_inclusion]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem incl_incl (F : S ≃ₐ[R] S) {k K L : ℕ} (h : k ∣ K) (h' : K ∣ L) (w : B ⊗[R] Lev F k) :
    incl B F h' (incl B F h w) = incl B F (h.trans h') w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmul_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module R M] (p : R) (N : ℕ)
    (hBN : algebraMap R B p ^ N = 0) (b : B) (y : M) : b ⊗ₜ[R] ((p ^ N) • y) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, map_pow, hBN, zero_mul,
    TensorProduct.zero_tmul]

theorem exists_level_preimage (F : S ≃ₐ[R] S) (p : R) (N : ℕ) (hBN : algebraMap R B p ^ N = 0)
    (happrox : ∀ x : S, ∃ k, 0 < k ∧ ∃ x' ∈ Lev F k, ∃ y : S, x - x' = algebraMap R S p ^ N * y)
    (z : B ⊗[R] S) : ∃ k, 0 < k ∧ ∃ w : B ⊗[R] Lev F k, ι B F k w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, 0, map_zero _⟩
  | tmul b x =>
    obtain ⟨k, hk, x', hx', y, hy⟩ := happrox x
    refine ⟨k, hk, b ⊗ₜ[R] ⟨x', hx'⟩, ?_⟩
    have hx : x = x' + (p ^ N) • y := by
      rw [Algebra.smul_def, map_pow, ← hy]; abel
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val, hx,
      TensorProduct.tmul_add, tmul_pow_smul_eq_zero B p N hBN, add_zero]
  | add x y hx hy =>
    obtain ⟨k₁, hk₁, w₁, rfl⟩ := hx
    obtain ⟨k₂, hk₂, w₂, rfl⟩ := hy
    refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂,
      incl B F (dvd_mul_right k₁ k₂) w₁ + incl B F (dvd_mul_left k₂ k₁) w₂, ?_⟩
    rw [map_add, ι_incl, ι_incl]

theorem comm_lTensor {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (u : B ⊗[R] N) :
    TensorProduct.comm R B P (LinearMap.lTensor B f u) = LinearMap.rTensor B f (TensorProduct.comm R B N u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lTensor_eq_zero_iff_rTensor_comm {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (u : B ⊗[R] N) :
    LinearMap.lTensor B f u = 0 ↔ LinearMap.rTensor B f (TensorProduct.comm R B N u) = 0 := by
  rw [← comm_lTensor, LinearEquiv.map_eq_zero_iff]

end Levels

section ZeroDetect

variable {R S : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
variable (B : Type) [CommRing B] [Algebra R B]

theorem exists_incl_eq_zero (F : S ≃ₐ[R] S) (p : R) (N : ℕ) (hBN : algebraMap R B p ^ N = 0)
    (happrox : ∀ x : S, ∃ k, 0 < k ∧ ∃ x' ∈ Lev F k, ∃ y : S, x - x' = algebraMap R S p ^ N * y)
    (hfin : ∀ k, 0 < k → Module.Finite R (Lev F k))
    {k : ℕ} (hk : 0 < k) (w : B ⊗[R] Lev F k) (hw : ι B F k w = 0) :
    ∃ l, 0 < l ∧ incl B F (dvd_mul_right k l) w = 0 := by
  classical
  set q : S := algebraMap R S p ^ N with hq_def
  set P : Submodule R S := LinearMap.range (LinearMap.mulLeft R q) with hP

  set M : ℕ → Submodule R (S ⧸ P) := fun j => (Lev F j).toSubmodule.map P.mkQ with hM
  have hMmono : ∀ {a b : ℕ}, a ∣ b → M a ≤ M b := by
    intro a b h
    simp only [hM]
    exact Submodule.map_mono (fun x hx => Lev_le_of_dvd F h hx)
  have hg_mem : ∀ (j : ℕ) (x : Lev F j), (P.mkQ ∘ₗ (Lev F j).val.toLinearMap) x ∈ M j :=
    fun j x => Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩
  set g : ∀ j : ℕ, Lev F j →ₗ[R] M j :=
    fun j => LinearMap.codRestrict (M j) (P.mkQ ∘ₗ (Lev F j).val.toLinearMap) (hg_mem j) with hg
  have hg_coe : ∀ (j : ℕ) (x : Lev F j), ((g j x : M j) : S ⧸ P) = P.mkQ (x : S) := fun j x => rfl

  have hsq : ∀ {a b : ℕ} (h : a ∣ b) (v : B ⊗[R] Lev F a),
      LinearMap.lTensor B (g b) (incl B F h v) =
        LinearMap.lTensor B (Submodule.inclusion (hMmono h)) (LinearMap.lTensor B (g a) v) := by
    intro a b h v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.lTensor_tmul]
      congr 1
    | add x y hx hy => simp only [map_add, hx, hy]

  have hcomp : ∀ (j : ℕ) (v : B ⊗[R] Lev F j),
      LinearMap.lTensor B (M j).subtype (LinearMap.lTensor B (g j) v) = LinearMap.lTensor B P.mkQ (ι B F j v) := by
    intro j v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.lTensor_tmul,
        Submodule.subtype_apply, hg_coe, Subalgebra.coe_val]
    | add x y hx hy => simp only [map_add, hx, hy]

  have hinj : ∀ K : ℕ, Function.Injective (LinearMap.lTensor B (g K)) := by
    intro K
    have hsurj : Function.Surjective (g K) := by
      rintro ⟨q', hq'⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hq'
      exact ⟨⟨y, hy⟩, rfl⟩
    have hex := lTensor_exact B (LinearMap.exact_subtype_ker_map (g K)) hsurj
    have h0 : LinearMap.lTensor B (LinearMap.ker (g K)).subtype = 0 := by
      refine TensorProduct.ext' fun b y => ?_
      obtain ⟨⟨x, hxK⟩, hx0⟩ := y
      have hxP : x ∈ P := by
        have h1 := congrArg (fun t : M K => (t : S ⧸ P)) (LinearMap.mem_ker.mp hx0)
        simp only [hg_coe, Submodule.mkQ_apply, Submodule.coe_zero] at h1
        exact (Submodule.Quotient.mk_eq_zero P).mp h1
      obtain ⟨s, hs⟩ := LinearMap.mem_range.mp hxP
      rw [LinearMap.mulLeft_apply] at hs
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, LinearMap.zero_apply]
      by_cases hq : q = 0
      · have hx : x = 0 := by rw [← hs, hq, zero_mul]
        have : (⟨x, hxK⟩ : Lev F K) = 0 := Subtype.ext hx
        rw [this, TensorProduct.tmul_zero]
      · have hsK : s ∈ Lev F K := by
          rw [mem_Lev]
          have hxK' := mem_Lev.mp hxK
          have hqfix : (F ^ K) q = q := by rw [hq_def, ← map_pow, AlgEquiv.commutes]
          rw [← hs, map_mul, hqfix] at hxK'
          exact mul_left_cancel₀ hq hxK'
        have : (⟨x, hxK⟩ : Lev F K) = (p ^ N) • (⟨s, hsK⟩ : Lev F K) := by
          apply Subtype.ext
          change x = ((p ^ N) • (⟨s, hsK⟩ : Lev F K) : S)
          rw [Algebra.smul_def, map_pow, ← hq_def]
          exact hs.symm
        rw [this, tmul_pow_smul_eq_zero B p N hBN]
    rw [h0] at hex
    exact LinearMap.ker_eq_bot.mp (by rw [hex.linearMap_ker_eq, LinearMap.range_zero])

  have hall : ∀ q' : S ⧸ P, ∃ j, 0 < j ∧ q' ∈ M j := by
    intro q'
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P q'
    obtain ⟨j, hj, x', hx', y, hy⟩ := happrox x
    refine ⟨j, hj, Submodule.mem_map.mpr ⟨x', hx', ?_⟩⟩
    symm
    apply (Submodule.Quotient.eq P).mpr
    exact LinearMap.mem_range.mpr ⟨y, by rw [LinearMap.mulLeft_apply, hy]⟩
  choose kq hkq_pos hkq_mem using hall

  have hMfg : (M k).FG := by
    haveI := hfin k hk
    exact (Module.Finite.iff_fg.mp (inferInstance : Module.Finite R (Lev F k))).map _

  set u := LinearMap.lTensor B (g k) w with hu_def
  have hu : LinearMap.lTensor B (M k).subtype u = 0 := by rw [hu_def, hcomp, hw, map_zero]
  have hu' : LinearMap.rTensor B (M k).subtype (TensorProduct.comm R B (M k) u) =
      LinearMap.rTensor B (M k).subtype 0 := by
    rw [map_zero]; exact (lTensor_eq_zero_iff_rTensor_comm B (M k).subtype u).mp hu
  obtain ⟨N', hN'fg, hle, heq⟩ := Submodule.FG.exists_rTensor_fg_inclusion_eq hMfg hu'
  rw [map_zero] at heq
  obtain ⟨s, hs⟩ := hN'fg
  set l := ∏ q' ∈ s, kq q' with hl_def
  have hl : 0 < l := Finset.prod_pos fun q' _ => hkq_pos q'
  have hN'le : N' ≤ M (k * l) := by
    rw [← hs]
    refine Submodule.span_le.mpr fun q' hq' => ?_
    exact hMmono ((Finset.dvd_prod_of_mem kq hq').mul_left k) (hkq_mem q')
  have hkl : M k ≤ M (k * l) := hMmono (dvd_mul_right k l)
  have hu2 : LinearMap.lTensor B (Submodule.inclusion hkl) u = 0 := by
    have : Submodule.inclusion hkl = Submodule.inclusion hN'le ∘ₗ Submodule.inclusion hle :=
      LinearMap.ext fun _ => rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply,
      (lTensor_eq_zero_iff_rTensor_comm B (Submodule.inclusion hle) u).mpr heq, map_zero]
  refine ⟨l, hl, hinj (k * l) ?_⟩
  rw [map_zero, hsq, ← hu_def, hu2]

end ZeroDetect

section Main

variable {R S : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
variable (B : Type) [CommRing B] [Algebra R B]

theorem exists_basis_of_existsUnique {T : Type} [AddCommGroup T] [Module R T] {k : ℕ} (v : Fin k → T)
    (h : ∀ x : T, ∃! c : Fin k → R, x = ∑ i, c i • v i) :
    ∃ bT : Module.Basis (Fin k) R T, ∀ i, bT i = v i := by
  have hli : LinearIndependent R v := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    have : g = 0 := (h 0).unique hg.symm (by simp)
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    obtain ⟨c, hc, -⟩ := h x
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

omit [IsDomain S] in
theorem ι_map_σ (F : S ≃ₐ[R] S) {k : ℕ} (σ : Lev F k ≃ₐ[R] Lev F k) (hσ : ∀ x : Lev F k, (σ x : S) = F x)
    (v : B ⊗[R] Lev F k) :
    ι B F k (Algebra.TensorProduct.map (AlgHom.id R B) (σ : Lev F k →ₐ[R] Lev F k) v) =
      Algebra.TensorProduct.map (AlgHom.id R B) (F : S →ₐ[R] S) (ι B F k v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsDomain S] in
theorem incl_map_σ (F : S ≃ₐ[R] S) {k K : ℕ} (h : k ∣ K)
    (σ : Lev F k ≃ₐ[R] Lev F k) (hσ : ∀ x : Lev F k, (σ x : S) = F x)
    (σ' : Lev F K ≃ₐ[R] Lev F K) (hσ' : ∀ x : Lev F K, (σ' x : S) = F x)
    (v : B ⊗[R] Lev F k) :
    incl B F h (Algebra.TensorProduct.map (AlgHom.id R B) (σ : Lev F k →ₐ[R] Lev F k) v) =
      Algebra.TensorProduct.map (AlgHom.id R B) (σ' : Lev F K →ₐ[R] Lev F K) (incl B F h v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom]
    congr 1
    apply Subtype.ext
    rw [Subalgebra.coe_inclusion, hσ, hσ', Subalgebra.coe_inclusion]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem existsUnique_generic (F : S ≃ₐ[R] S) (p : R) (N : ℕ) (hBN : algebraMap R B p ^ N = 0)
    (happrox : ∀ x : S, ∃ k, 0 < k ∧ ∃ x' ∈ Lev F k, ∃ y : S, x - x' = algebraMap R S p ^ N * y)
    (hlev : ∀ k, 0 < k → ∃ (ζ : Lev F k) (σ : Lev F k ≃ₐ[R] Lev F k),
        (∀ x : Lev F k, (σ x : S) = F x) ∧
        (∀ x : Lev F k, ∃! c : Fin k → R, x = ∑ i : Fin k, c i • ζ ^ (i : ℕ)) ∧
        (∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)))
    (z : B ⊗[R] S) (hz : Algebra.TensorProduct.map (AlgHom.id R B) (F : S →ₐ[R] S) z = z) :
    ∃! b : B, z = b ⊗ₜ[R] (1 : S) := by

  have hbasis : ∀ k, 0 < k → ∃ (ζ : Lev F k) (σ : Lev F k ≃ₐ[R] Lev F k) (bT : Module.Basis (Fin k) R (Lev F k)),
      (∀ x : Lev F k, (σ x : S) = F x) ∧ (∀ i, bT i = ζ ^ (i : ℕ)) ∧
      (∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)) := by
    intro k hk
    obtain ⟨ζ, σ, hσ, hb, hu⟩ := hlev k hk
    obtain ⟨bT, hbT⟩ := exists_basis_of_existsUnique (fun i : Fin k => ζ ^ (i : ℕ)) hb
    exact ⟨ζ, σ, bT, hσ, hbT, hu⟩
  have hfin : ∀ k, 0 < k → Module.Finite R (Lev F k) := by
    intro k hk
    obtain ⟨-, -, bT, -, -, -⟩ := hbasis k hk
    exact Module.Finite.of_basis bT

  obtain ⟨k, hk, w, rfl⟩ := exists_level_preimage B F p N hBN happrox z
  obtain ⟨ζ, σ, bT, hσ, hbT, hunit⟩ := hbasis k hk
  set d := Algebra.TensorProduct.map (AlgHom.id R B) (σ : Lev F k →ₐ[R] Lev F k) w - w with hd_def
  have hd : ι B F k d = 0 := by rw [hd_def, map_sub, ι_map_σ B F σ hσ, hz, sub_self]
  obtain ⟨l, hl, hdl⟩ := exists_incl_eq_zero B F p N hBN happrox hfin hk d hd
  obtain ⟨ζ', σ', bT', hσ', hbT', hunit'⟩ := hbasis (k * l) (Nat.mul_pos hk hl)
  set w' := incl B F (dvd_mul_right k l) w with hw'_def
  have hw'fix : Algebra.TensorProduct.map (AlgHom.id R B) (σ' : Lev F (k * l) →ₐ[R] Lev F (k * l)) w' = w' := by
    rw [← sub_eq_zero, hw'_def, ← incl_map_σ B F (dvd_mul_right k l) σ hσ σ' hσ', ← map_sub, ← hd_def, hdl]
  obtain ⟨b, hb⟩ := level_descent (k * l) (Nat.mul_pos hk hl) ζ' σ' bT' hbT' hunit' w' hw'fix
  have hzb : ι B F k w = b ⊗ₜ[R] (1 : S) := by
    rw [← ι_incl B F (dvd_mul_right k l) w, ← hw'_def, hb, Algebra.TensorProduct.map_tmul]
    simp
  refine ⟨b, hzb, fun b' hb' => ?_⟩

  have h0 : ι B F 1 ((b' - b) ⊗ₜ[R] (1 : Lev F 1)) = 0 := by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one, TensorProduct.sub_tmul, ← hb', ← hzb,
      sub_self]
  obtain ⟨l₁, hl₁, h1⟩ := exists_incl_eq_zero B F p N hBN happrox hfin one_pos _ h0
  rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one] at h1
  obtain ⟨ζ₁, σ₁, bT₁, -, hbT₁, -⟩ := hbasis (1 * l₁) (Nat.mul_pos one_pos hl₁)
  have := eq_zero_of_tmul_one_eq_zero bT₁ ⟨0, Nat.mul_pos one_pos hl₁⟩ (by rw [hbT₁]; simp) (b' - b) h1
  exact (sub_eq_zero.mp this)

end Main

end CerednikDrinfeld.FormalOmega.AffineDescentAux

open scoped NumberField TensorProduct
p2m_open "CategoryTheory CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq.CerednikDrinfeld.FormalOmega"

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    ∀ z : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr,
      Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) z = z →
      ∃! b : B, z = b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr) := by
  intro z hz
  obtain ⟨happroxT, hlevT⟩ := CerednikDrinfeld.FormalOmega.fixedPoints_frobenius_levels 𝒪 hdvr π hπ hcomplete
    hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS
  obtain ⟨N, hN⟩ := hB
  have hπmem : algebraMap 𝒪 Onr π ∈ AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr) := by
    rw [AlgHom.mem_equalizer]
    simp
  set p : ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) := ⟨algebraMap 𝒪 Onr π, hπmem⟩ with hp_def
  have hp : algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr p = algebraMap 𝒪 Onr π := rfl
  have hBN : algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B p ^ N = 0 := by
    have h1 : algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π = p := Subtype.ext (by rw [hp_def]; exact Subalgebra.coe_algebraMap _ π)
    rw [← h1, ← IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B π]
    exact hN
  refine CerednikDrinfeld.FormalOmega.AffineDescentAux.existsUnique_generic B FrS p N hBN ?_ ?_ z hz
  · intro x
    obtain ⟨k, hk, x', hx', hmem⟩ := happroxT N x
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨k, hk, x', hx', y, by rw [hp, ← hy, mul_comm]⟩
  · intro k hk
    obtain ⟨ζ, σ, h1, h2, h3, -⟩ := hlevT k hk
    exact ⟨ζ, σ, h1, h2, h3⟩

end S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq (solution)
