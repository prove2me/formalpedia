-- Prove2me | solution 1 for Deformation.DieudonneModule.map_surjective_and_exact_map_of_ker_eq_map_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7149a408-71d4-5424-855b-d9d4ce95ee66

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Theorems.Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w x

namespace KerDieudonne

section Unip

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

theorem toDual_pow (γ : CartierDual k A) (m : ℕ) :
    CartierDual.toDual k A (γ ^ (m + 1)) = ((WithConv.toConv (CartierDual.toDual k A γ)) ^ (m + 1)).ofConv := by
  induction m with
  | zero => rw [zero_add, pow_one, pow_one, WithConv.ofConv_toConv]
  | succ m ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem exists_forall_convPow_eq_zero (hA : IsLocalRing (CartierDual k A)) :
    ∃ n : ℕ, ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0 := by
  haveI : IsLocalRing (CartierDual k A) := hA
  haveI : IsArtinianRing (CartierDual k A) := IsArtinianRing.of_finite k (CartierDual k A)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  refine ⟨N + 1, fun β hβ => ?_⟩
  set γ : CartierDual k A := CartierDual.ofDual k A β.ofConv with hγ
  have hγ1 : γ ∈ IsLocalRing.maximalIdeal (CartierDual k A) := by
    have hk : γ ∈ RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k A)) := by
      rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
      erw [CartierDual.counit_apply]
      rw [hγ]
      simpa [CartierDual.ofDual_apply] using hβ
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) hk
  have hγN : γ ^ (N + 1) = 0 := by
    have : γ ^ (N + 1) ∈ IsLocalRing.maximalIdeal (CartierDual k A) ^ (N + 1) :=
      Ideal.pow_mem_pow hγ1 _
    rw [pow_succ, hN, Ideal.zero_eq_bot, Ideal.bot_mul] at this
    exact this
  have hβN : β ^ (N + 1) = 0 := by
    have h2 : β ^ (N + 1) = WithConv.toConv (CartierDual.toDual k A (γ ^ (N + 1))) := by
      rw [toDual_pow, WithConv.toConv_ofConv, hγ, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]
    rw [h2, hγN, map_zero]
    rfl
  exact pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hβN

end Unip

section Witt

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]

theorem coeff_mem_hopfKer_of_map_eq_zero (q : A →ₐc[k] B) {χ : TruncatedWittVector p n A}
    (hχ : χ ∈ Deformation.wittHom k p n A)
    (h0 : Deformation.TruncWitt.map (q : A →ₐ[k] B).toRingHom χ = 0) (i : Fin n) :
    χ.coeff i ∈ HopfAlgebra.hopfKer q := by
  rw [HopfAlgebra.mem_hopfKer_iff]
  rw [Deformation.mem_wittHom_iff] at hχ

  have h := congrArg (Deformation.TruncWitt.map (p := p) (n := n)
    (Algebra.TensorProduct.map (AlgHom.id k A) (q : A →ₐ[k] B)).toRingHom) hχ
  rw [map_add, Deformation.TruncWitt.map_map, Deformation.TruncWitt.map_map,
    Deformation.TruncWitt.map_map] at h
  have e1 : (Algebra.TensorProduct.map (AlgHom.id k A) (q : A →ₐ[k] B)).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom := by
    ext a; simp
  have e2 : (Algebra.TensorProduct.map (AlgHom.id k A) (q : A →ₐ[k] B)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toRingHom =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom.comp
        (q : A →ₐ[k] B).toRingHom := by
    ext a; simp
  have e3 : Deformation.TruncWitt.map (p := p) (n := n)
      ((Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom.comp (q : A →ₐ[k] B).toRingHom) χ =
      Deformation.TruncWitt.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
        (Deformation.TruncWitt.map (q : A →ₐ[k] B).toRingHom χ) :=
    (Deformation.TruncWitt.map_map _ _ _).symm
  rw [e1, e2, e3, h0, map_zero, add_zero] at h
  have := congrArg (TruncatedWittVector.coeff i) h
  simp only [Deformation.TruncWitt.coeff_map, RingHom.coe_comp, Function.comp_apply] at this
  exact this

theorem comp_apply_eq_algebraMap_counit {A' : Type x} [CommRing A'] [HopfAlgebra k A']
    (φ : A' →ₐc[k] A) (q : A →ₐc[k] B)
    (hexact : RingHom.ker (q : A →ₐ[k] B) =
      Ideal.map (φ : A' →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k A'))) (a : A') :
    q (φ a) = algebraMap k B (Coalgebra.counit (R := k) a) := by
  have ha : a - algebraMap k A' (Coalgebra.counit (R := k) a) ∈
      RingHom.ker (Bialgebra.counitAlgHom k A') := by
    rw [RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Bialgebra.counit_algebraMap, sub_self]
  have : φ (a - algebraMap k A' (Coalgebra.counit (R := k) a)) ∈ RingHom.ker (q : A →ₐ[k] B) := by
    rw [hexact]; exact Ideal.mem_map_of_mem _ ha
  rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at this
  have e : φ (algebraMap k A' (Coalgebra.counit (R := k) a)) = algebraMap k A (Coalgebra.counit (R := k) a) :=
    AlgHomClass.commutes φ _
  change q (φ a) = q (φ (algebraMap k A' (Coalgebra.counit (R := k) a))) at this
  rw [e, AlgHomClass.commutes] at this
  exact this

end Witt

end KerDieudonne

open KerDieudonne in
theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (A' : Type v) [CommRing A'] [HopfAlgebra k A'] [Coalgebra.IsCocomm k A'] [Module.Finite k A']
    (A : Type w) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (hA' : IsLocalRing (CartierDual k A')) (hA : IsLocalRing (CartierDual k A))
    (B : Type x) [CommRing B] [Bialgebra k B]
    (φ : A' →ₐc[k] A) (q : A →ₐc[k] B) (hq : Function.Surjective q)
    (hexact : RingHom.ker (q : A →ₐ[k] B) =
      Ideal.map (φ : A' →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k A'))) :
    Function.Surjective (Deformation.DieudonneModule.map k p q) ∧
      Function.Exact (Deformation.DieudonneModule.map k p φ)
        (Deformation.DieudonneModule.map k p q) := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  obtain ⟨n₀, hn₀⟩ := exists_forall_convPow_eq_zero k p A hA
  obtain ⟨n₀', hn₀'⟩ := exists_forall_convPow_eq_zero k p A' hA'

  have hV : ∀ N, n₀ ≤ N → ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ N = 0 :=
    fun N hN β hβ => pow_eq_zero_of_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hN) (hn₀ β hβ)
  have hV' : ∀ N, n₀' ≤ N → ∀ β : WithConv (A' →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ N = 0 :=
    fun N hN β hβ => pow_eq_zero_of_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hN) (hn₀' β hβ)
  refine ⟨?_, ?_⟩
  ·
    intro z
    obtain ⟨n, y, rfl⟩ := Deformation.DieudonneModule.exists_of z
    set N := n + n₀ + 1 with hN
    haveI : NeZero N := ⟨by omega⟩
    have hnN : n ≤ N := by omega
    obtain ⟨x, hx⟩ :=
      HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p N A B q hq
        (hV N (by omega)) (Deformation.wittHomShiftLE k p B hnN y)
    refine ⟨Deformation.DieudonneModule.of k p A N x, ?_⟩
    rw [Deformation.DieudonneModule.map_of, hx, Deformation.DieudonneModule.of_shiftLE]
  ·
    intro y
    constructor
    ·
      intro hy
      obtain ⟨n, χ, rfl⟩ := Deformation.DieudonneModule.exists_of y
      rw [Deformation.DieudonneModule.map_of] at hy
      have h0 : Deformation.wittHomMap p n q χ = 0 :=
        Deformation.DieudonneModule.of_injective n (by rw [hy, map_zero])
      have h0' : Deformation.TruncWitt.map (q : A →ₐ[k] B).toRingHom (χ : TruncatedWittVector p n A) = 0 := by
        have := congrArg Subtype.val h0
        simpa [Deformation.coe_wittHomMap] using this

      obtain ⟨Q, _, _, _, _, π', ι, hπ', hι, hιπ, hΔ, hS⟩ :=
        HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
          (R := k) φ
      haveI : Algebra.FiniteType k A := Module.Finite.finiteType A
      have hkerq : RingHom.ker (q : A →+* B) =
          Ideal.span {x : A | x ∈ (φ : A' →ₐ[k] A).range ∧ Coalgebra.counit (R := k) x = 0} := by
        have h1 : RingHom.ker (q : A →+* B) = RingHom.ker (q : A →ₐ[k] B) := rfl
        rw [h1, hexact, Ideal.map]
        congr 1
        ext x
        simp only [Set.mem_image, SetLike.mem_coe, RingHom.mem_ker, Bialgebra.counitAlgHom_apply,
          Set.mem_setOf_eq, AlgHom.mem_range]
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨a, rfl⟩, ?_⟩
          change Coalgebra.counit (R := k) (φ a) = 0
          rw [CoalgHomClass.counit_comp_apply]; exact ha
        · rintro ⟨⟨a, rfl⟩, hx⟩
          refine ⟨a, ?_, rfl⟩
          change Coalgebra.counit (R := k) (φ a) = 0 at hx
          rw [CoalgHomClass.counit_comp_apply] at hx; exact hx
      have hHK := HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span (φ : A' →ₐ[k] A).range hΔ hS q hq hkerq

      have hcoef : ∀ i : Fin n, ∃ c : Q, ι c = (χ : TruncatedWittVector p n A).coeff i := by
        intro i
        have hi := coeff_mem_hopfKer_of_map_eq_zero q χ.2 h0' i
        rw [hHK, AlgHom.mem_range] at hi
        obtain ⟨a, ha⟩ := hi
        refine ⟨π' a, ?_⟩
        rw [← ha, ← hιπ]
        rfl
      choose c hc using hcoef
      let cw : TruncatedWittVector p n Q := TruncatedWittVector.mk p c
      have hcw : Deformation.TruncWitt.map (ι : Q →ₐ[k] A).toRingHom cw = (χ : TruncatedWittVector p n A) := by
        ext i
        rw [Deformation.TruncWitt.coeff_map]
        simp [cw, hc]

      have hinjιι : Function.Injective
          (Algebra.TensorProduct.map (ι : Q →ₐ[k] A) (ι : Q →ₐ[k] A)) := by
        show Function.Injective (TensorProduct.map (ι : Q →ₐ[k] A).toLinearMap (ι : Q →ₐ[k] A).toLinearMap)
        exact TensorProduct.map_injective_of_flat_flat' _ _ hι hι
      have hcw_mem : cw ∈ Deformation.wittHom k p n Q := by
        rw [Deformation.mem_wittHom_iff]
        apply Deformation.TruncWitt.map_injective
          (f := (Algebra.TensorProduct.map (ι : Q →ₐ[k] A) (ι : Q →ₐ[k] A)).toRingHom) hinjιι
        have hΔ' : (Algebra.TensorProduct.map (ι : Q →ₐ[k] A) (ι : Q →ₐ[k] A)).toRingHom.comp
            (Deformation.comulRingHom k Q) = (Deformation.comulRingHom k A).comp (ι : Q →ₐ[k] A).toRingHom := by
          refine RingHom.ext fun a => ?_
          exact AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom ι) a
        have h₁ : (Algebra.TensorProduct.map (ι : Q →ₐ[k] A) (ι : Q →ₐ[k] A)).toRingHom.comp
            (Algebra.TensorProduct.includeLeft : Q →ₐ[k] Q ⊗[k] Q).toRingHom =
            (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom.comp (ι : Q →ₐ[k] A).toRingHom := by
          refine RingHom.ext fun a => ?_; simp
        have h₂ : (Algebra.TensorProduct.map (ι : Q →ₐ[k] A) (ι : Q →ₐ[k] A)).toRingHom.comp
            (Algebra.TensorProduct.includeRight : Q →ₐ[k] Q ⊗[k] Q).toRingHom =
            (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toRingHom.comp (ι : Q →ₐ[k] A).toRingHom := by
          refine RingHom.ext fun a => ?_; simp
        rw [map_add, Deformation.TruncWitt.map_map, Deformation.TruncWitt.map_map,
          Deformation.TruncWitt.map_map, hΔ', h₁, h₂, ← Deformation.TruncWitt.map_map,
          ← Deformation.TruncWitt.map_map, ← Deformation.TruncWitt.map_map, hcw]
        exact (Deformation.mem_wittHom_iff _).1 χ.2

      set N := n + n₀' + 1 with hN
      haveI : NeZero N := ⟨by omega⟩
      have hnN : n ≤ N := by omega
      obtain ⟨x, hx⟩ :=
        HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p N A' Q π' hπ'
          (hV' N (by omega)) (Deformation.wittHomShiftLE k p Q hnN ⟨cw, hcw_mem⟩)
      refine ⟨Deformation.DieudonneModule.of k p A' N x, ?_⟩
      have hφx : Deformation.wittHomMap p N φ x =
          Deformation.wittHomMap p N ι (Deformation.wittHomMap p N π' x) := by
        apply Subtype.ext
        simp only [Deformation.coe_wittHomMap, Deformation.TruncWitt.map_map]
        congr 1
        rw [← hιπ]; rfl
      rw [Deformation.DieudonneModule.map_of, hφx, hx, Deformation.wittHomMap_shiftLE,
        Deformation.DieudonneModule.of_shiftLE]
      congr 1
      exact Subtype.ext hcw
    ·
      rintro ⟨z, rfl⟩
      obtain ⟨n, χ, rfl⟩ := Deformation.DieudonneModule.exists_of z
      rw [Deformation.DieudonneModule.map_of, Deformation.DieudonneModule.map_of]
      convert map_zero (Deformation.DieudonneModule.of k p B n)
      apply Subtype.ext
      simp only [Deformation.coe_wittHomMap, Deformation.TruncWitt.map_map, ZeroMemClass.coe_zero]
      ext i
      rw [Deformation.TruncWitt.coeff_map, TruncatedWittVector.coeff_zero, RingHom.comp_apply]
      change q (φ ((χ : TruncatedWittVector p n A').coeff i)) = 0
      rw [comp_apply_eq_algebraMap_counit φ q hexact, Deformation.counit_coeff_of_mem_wittHom χ.2 i,
        map_zero]

end S_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit
end P2MW
export P2MW.S_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit (solution)
