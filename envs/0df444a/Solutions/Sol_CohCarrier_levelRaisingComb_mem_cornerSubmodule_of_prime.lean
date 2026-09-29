-- Prove2me | solution 1 for CohCarrier.levelRaisingComb_mem_cornerSubmodule_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2db1dbf2-c52a-5f4b-a5f4-5946515d2b9c

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_heckeT_comb_eq_zero
import Theorems.Thm_CohCarrier_iDeg_comp
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace LevelRaisingCornerSol

open CohCarrier IharaLemma
open scoped IsMulCommutative MatrixGroups
open CongruenceSubgroup

section Abstract

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)

theorem one_sub_e_mem_iff (i j : Fin S.n) : 1 - S.e i ∈ S.𝔪 j ↔ j = i := by
  constructor
  · intro h
    by_contra hji
    have hei : S.e i ∈ S.𝔪 j := S.mem_of_ne (fun h' => hji h'.symm)
    have : (1 : B) ∈ S.𝔪 j := by
      have := (S.𝔪 j).add_mem h hei
      rwa [sub_add_cancel] at this
    exact (S.isMaximal j).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · rintro rfl
    have hsum : ∑ i, S.e i = 1 := S.coi.complete
    classical
    have : 1 - S.e j = ∑ i ∈ Finset.univ.erase j, S.e i := by
      rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_sub_cancel_right]
    rw [this]
    refine Ideal.sum_mem _ fun i hi => ?_
    exact S.mem_of_ne (Finset.ne_of_mem_erase hi)

variable {M : Type} [AddCommGroup M] [Module B M]

theorem mem_cornerSubmodule_iff (e : B) (he : IsIdempotentElem e) (v : M) :
    v ∈ cornerSubmodule (M := M) e ↔ e • v = v := by
  constructor
  · rintro ⟨v₀, rfl⟩
    show e • (e • v₀) = e • v₀
    rw [smul_smul, he.eq]
  · intro h
    exact ⟨v, h⟩

theorem mem_corner_iff_forall_smul_eq_zero (i : Fin S.n) (v : M) :
    v ∈ cornerSubmodule (M := M) (S.e i) ↔ ∀ j, j ≠ i → S.e j • v = 0 := by
  rw [mem_cornerSubmodule_iff _ (S.idem i)]
  constructor
  · intro h j hji
    rw [← h, smul_smul, S.coi.ortho hji, zero_smul]
  · intro h
    classical
    have hsum : ∑ j, S.e j = 1 := S.coi.complete
    calc S.e i • v = (∑ j, S.e j) • v - ∑ j ∈ Finset.univ.erase i, S.e j • v := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_smul, Finset.sum_smul,
              add_sub_cancel_left]
      _ = v := by
            rw [hsum, one_smul, Finset.sum_eq_zero (fun j hj => h j (Finset.ne_of_mem_erase hj)),
              sub_zero]

theorem e_smul_eq_zero_of_smul_eq_zero (j : Fin S.n) {s : B} (hs : s ∉ S.𝔪 j) {v : M}
    (hv : s • v = 0) : S.e j • v = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem j) (S.𝔪 j) (S.mem_of_isMaximal_of_ne j) hs
  rw [← ht, mul_comm t s, mul_assoc, mul_comm s, mul_smul, hv, smul_zero]

variable {F : Type} [CommRing F] {B' : Type} [CommRing B'] (S' : IdempotentSplitting B')
  {M' : Type} [AddCommGroup M'] [Module B' M']

theorem map_mem_cornerSubmodule_of_comap_eq (ψ : F →+* B) (ψ' : F →+* B')
    (hψ : Function.Surjective ψ) (hψ' : Function.Surjective ψ')
    (i : Fin S.n) (i' : Fin S'.n) (hcomap : (S.𝔪 i).comap ψ = (S'.𝔪 i').comap ψ')
    (w : M →+ M') (hw : ∀ (f : F) (v : M), w (ψ f • v) = ψ' f • w v)
    (v : M) (hv : v ∈ cornerSubmodule (M := M) (S.e i)) :
    w v ∈ cornerSubmodule (M := M') (S'.e i') := by
  rw [mem_corner_iff_forall_smul_eq_zero]
  intro j hj

  have hex : ∃ g : F, ψ g ∈ Ideal.span {1 - S.e i} ∧ ψ' g ∉ S'.𝔪 j := by
    by_contra hne
    push Not at hne

    have hle : (Ideal.span {1 - S.e i}).comap ψ ≤ (S'.𝔪 j).comap ψ' := fun g hg => hne g hg
    have hker : RingHom.ker ψ ≤ (S'.𝔪 j).comap ψ' :=
      le_trans (fun g hg => by
        rw [Ideal.mem_comap, RingHom.mem_ker.mp hg]; exact Ideal.zero_mem _) hle
    haveI hPmax : ((S'.𝔪 j).comap ψ').IsMaximal := Ideal.comap_isMaximal_of_surjective ψ' hψ'

    set Q : Ideal B := ((S'.𝔪 j).comap ψ').map ψ with hQ
    have hQP : Q.comap ψ = (S'.𝔪 j).comap ψ' := by
      rw [hQ, Ideal.comap_map_of_surjective ψ hψ, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker]
    have hQmax : Q.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective ψ hψ hPmax with h | h
      · exfalso
        apply hPmax.ne_top
        rw [← hQP, hQ, h, Ideal.comap_top]
      · exact h
    have h1e : 1 - S.e i ∈ Q := by
      obtain ⟨g₀, hg₀⟩ := hψ (1 - S.e i)
      have : g₀ ∈ (S'.𝔪 j).comap ψ' := hle (by
        rw [Ideal.mem_comap, hg₀]; exact Ideal.mem_span_singleton_self _)
      rw [← hg₀]
      exact Ideal.mem_map_of_mem ψ this
    obtain ⟨j₀, hj₀⟩ := S.exists_eq Q hQmax
    have hj₀i : j₀ = i := (one_sub_e_mem_iff S i j₀).mp (hj₀ ▸ h1e)
    subst hj₀i

    have hcm : (S'.𝔪 j).comap ψ' = (S'.𝔪 i').comap ψ' := by rw [← hQP, ← hj₀, hcomap]
    have : S'.𝔪 j = S'.𝔪 i' := by
      rw [← Ideal.map_comap_of_surjective ψ' hψ' (S'.𝔪 j), hcm,
        Ideal.map_comap_of_surjective ψ' hψ']
    exact hj (S'.𝔪_injective this)
  obtain ⟨g, hg, hg'⟩ := hex
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hg
  refine e_smul_eq_zero_of_smul_eq_zero S' j hg' ?_
  rw [← hw, ← hb]
  have hv' : (1 - S.e i) • v = 0 := by
    rw [sub_smul, one_smul, (mem_cornerSubmodule_iff _ (S.idem i) v).mp hv, sub_self]
  rw [mul_smul, hv', smul_zero, map_zero]

end Abstract

section DiamondTop

variable (M : ℕ) [NeZero M] (A : Type) [AddCommGroup A]

theorem diamondRaw_top_eq_self (σ : Gamma0 M) (φ : H1 M ⊤ A) : diamondRaw M ⊤ A σ φ = φ := by
  have hσ : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := mem_GammaH_iff.mpr ⟨σ.2, Subgroup.mem_top _⟩
  set κ : ↥(GammaH M ⊤) := ⟨(σ : SL(2, ℤ)), hσ⟩ with hκ
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (conjHom M ⊤ σ (Additive.toMul a))) = φ a
  have hconj : conjHom M ⊤ σ (Additive.toMul a) = κ * Additive.toMul a * κ⁻¹ := by
    apply Subtype.ext
    simp [conjHom, hκ]
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

theorem diamondL_top_eq_one (𝒪 : Type) [CommRing 𝒪] (d : (ZMod M)ˣ) :
    diamondL M ⊤ 𝒪 d = 1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M d
  refine LinearMap.ext fun φ => ?_
  rw [diamondL_eq_diamondRaw M ⊤ 𝒪 d σ hσ φ, diamondRaw_top_eq_self]
  rfl

end DiamondTop

section Hecke

variable (M : ℕ) [NeZero M] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen M S,
      opFamily M ⊤ S 𝒪 g * opFamily M ⊤ S 𝒪 g' = opFamily M ⊤ S 𝒪 g' * opFamily M ⊤ S 𝒪 g)
  (θbar : Gen M S → k)

local notation3 "𝕋" => (CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra

noncomputable def gOp (g : Gen M S) : ↥𝕋 :=
  ⟨(hdata M ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

@[scoped simp] theorem coe_gOp (g : Gen M S) :
    ((gOp M S 𝒪 k hcomm θbar g : ↥𝕋) : Module.End 𝒪 (H1 M ⊤ 𝒪)) = opFamily M ⊤ S 𝒪 g := rfl

theorem subalg_smul_def (b : ↥𝕋) (m : H1 M ⊤ 𝒪) :
    b • m = (b : Module.End 𝒪 (H1 M ⊤ 𝒪)) m := rfl

theorem gOp_dia_eq_one (d : (ZMod M)ˣ) : gOp M S 𝒪 k hcomm θbar (Gen.dia d) = 1 := by
  apply Subtype.ext
  rw [coe_gOp, Subalgebra.coe_one]
  exact diamondL_top_eq_one M 𝒪 d

noncomputable def freeToT : MvPolynomial (Gen M S) 𝒪 →ₐ[𝒪] ↥𝕋 :=
  MvPolynomial.aeval (gOp M S 𝒪 k hcomm θbar)

theorem freeToT_X (g : Gen M S) : freeToT M S 𝒪 k hcomm θbar (MvPolynomial.X g) = gOp M S 𝒪 k hcomm θbar g := by
  simp [freeToT]

theorem freeToT_C (r : 𝒪) : freeToT M S 𝒪 k hcomm θbar (MvPolynomial.C r) = algebraMap 𝒪 ↥𝕋 r :=
  MvPolynomial.aeval_C _ r

theorem surjective_of_forall_gOp_mem_range {G : Type} (ψ : MvPolynomial G 𝒪 →ₐ[𝒪] ↥𝕋)
    (hψ : ∀ g : Gen M S, ∃ f, ψ f = gOp M S 𝒪 k hcomm θbar g) : Function.Surjective ψ := by
  intro x
  obtain ⟨x, hx⟩ := x
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · rintro _ ⟨g, rfl⟩
    obtain ⟨f, hf⟩ := hψ g
    exact ⟨f, hf⟩
  · intro r
    exact ⟨algebraMap 𝒪 _ r, by rw [AlgHom.commutes]; rfl⟩
  · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [map_add, hf, hg]; rfl⟩
  · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, by rw [map_mul, hf, hg]; rfl⟩

theorem freeToT_surjective : Function.Surjective (freeToT M S 𝒪 k hcomm θbar) :=
  surjective_of_forall_gOp_mem_range M S 𝒪 k hcomm θbar _ fun g =>
    ⟨MvPolynomial.X g, freeToT_X M S 𝒪 k hcomm θbar g⟩

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

noncomputable def toCornerAlg : ↥𝕋 →ₐ[𝒪] Sp.CornerRing i₀ where
  toFun := Sp.toCornerRing i₀
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := rfl

@[scoped simp] theorem toCornerAlg_apply (b : ↥𝕋) : toCornerAlg M S 𝒪 k hcomm θbar Sp i₀ b = Sp.toCornerRing i₀ b := rfl

variable (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)

theorem toCornerRing_one_sub_e : Sp.toCornerRing i₀ (1 - Sp.e i₀) = 0 := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_toCornerRing]
  show Sp.e i₀ * (1 - Sp.e i₀) * Sp.e i₀ = 0
  linear_combination (-Sp.e i₀) * (Sp.idem i₀).eq

theorem 𝔪_eq_ker (hk : Function.Surjective (algebraMap 𝒪 k)) :
    Sp.𝔪 i₀ = RingHom.ker (πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀)) := by
  set χ : ↥𝕋 →ₐ[𝒪] k := πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀) with hχ
  have hsurj : Function.Surjective χ := fun x => by
    obtain ⟨r, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 _ r, χ.commutes r⟩
  haveI hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have h1e : (1 : ↥𝕋) - Sp.e i₀ ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, hχ, AlgHom.comp_apply, toCornerAlg_apply, toCornerRing_one_sub_e, map_zero]
  rw [← hj] at h1e ⊢
  rw [(one_sub_e_mem_iff Sp i₀ j).mp h1e]

theorem gOp_T_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_U_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.U ℓ hℓ hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_dia_smul (d : (ZMod M)ˣ) (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.dia d)) • v = v := by
  rw [gOp_dia_eq_one, one_smul]

theorem algebraMap_smul_eq (r : 𝒪) (v : H1 M ⊤ 𝒪) : (algebraMap 𝒪 ↥𝕋 r) • v = r • v :=
  algebraMap_smul _ r v

theorem comap_𝔪_eq_ker_aeval (hk : Function.Surjective (algebraMap 𝒪 k)) {G : Type}
    (ψ : MvPolynomial G 𝒪 →ₐ[𝒪] ↥𝕋) :
    (Sp.𝔪 i₀).comap ψ =
      RingHom.ker (MvPolynomial.aeval (R := 𝒪)
        (fun g => πk (Sp.toCornerRing i₀ (ψ (MvPolynomial.X g))))) := by
  have hfun : (πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀)).comp ψ =
      MvPolynomial.aeval (R := 𝒪) (fun g => πk (Sp.toCornerRing i₀ (ψ (MvPolynomial.X g)))) := by
    apply MvPolynomial.algHom_ext
    intro g
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, toCornerAlg_apply]
  rw [𝔪_eq_ker M S 𝒪 k hcomm θbar Sp i₀ πk hk, ← hfun]
  ext f
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.comp_apply]

end Hecke

section Levels

theorem levelLE_top {M M' d : ℕ} (hM : M ∣ M') (hd : d ∣ M' / M) :
    LevelLE M M' (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod M')ˣ) d :=
  ⟨hM, hd, fun _ _ => Subgroup.mem_top _⟩

theorem iDeg'_congr_d {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type} [AddCommGroup A] {d d' : ℕ} (hd : d = d') [NeZero d] [NeZero d']
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d') (φ : H1 M H A) :
    iDeg' M M' H H' d A h φ = iDeg' M M' H H' d' A h' φ := by
  subst hd
  rfl

variable {N q : ℕ} [NeZero N] [NeZero q] (hqp : q.Prime) (hqN : ¬ q ∣ N) {A : Type} [AddCommGroup A]

theorem levelLE_one_Nq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1 :=
  levelLE_top (dvd_mul_right N q) (one_dvd _)

theorem levelLE_q_Nq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q :=
  levelLE_top (dvd_mul_right N q) (by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))])

theorem levelLE_one_Nq_Nq2 :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1 :=
  levelLE_top (by rw [pow_two, ← mul_assoc]; exact dvd_mul_right _ q) (one_dvd _)

theorem levelLE_q_Nq_Nq2 :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q :=
  levelLE_top (by rw [pow_two, ← mul_assoc]; exact dvd_mul_right _ q) (by
    rw [pow_two, ← mul_assoc, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne (N * q)))])

theorem levelLE_N_Nq2 (d : ℕ) (hd : d ∣ q * q) :
    LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) d :=
  levelLE_top (dvd_mul_right N _) (by
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)), pow_two])

include hqp hqN in

theorem heckeT_comb_eq_zero_gen (M₃ : ℕ) [NeZero M₃] (e : N * q * q = M₃)
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (h₁' : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) 1)
    (hq' : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT M₃ ⊤ q A
        (q • iDeg' (N * q) M₃ ⊤ ⊤ 1 A h₁' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
          - iDeg' (N * q) M₃ ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ))
          + iDeg' (N * q) M₃ ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq φ)) = 0 := by
  subst e
  exact heckeT_comb_eq_zero h₁ hqp hqN hq h₁' hq' φ

include hqp hqN in

theorem heckeT_levelRaisingComb_eq_zero
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (φ : H1 N ⊤ A) :
    heckeT (N * q ^ 2) ⊤ q A
        (q • iDeg' N (N * q ^ 2) ⊤ ⊤ 1 A h1 φ
          - iDeg' N (N * q ^ 2) ⊤ ⊤ q A hq' (heckeT N ⊤ q A φ)
          + iDeg' N (N * q ^ 2) ⊤ ⊤ (q ^ 2) A hq2 φ) = 0 := by
  have h := heckeT_comb_eq_zero_gen hqp hqN (A := A) (N * q ^ 2) (by ring)
    levelLE_one_Nq levelLE_q_Nq levelLE_one_Nq_Nq2 levelLE_q_Nq_Nq2 φ
  haveI : NeZero (1 * 1) := ⟨by norm_num⟩
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact NeZero.ne q⟩
  haveI : NeZero (q * q) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
  rw [← iDeg_comp levelLE_one_Nq levelLE_one_Nq_Nq2 (levelLE_N_Nq2 (1 * 1) (by simp)),
    ← iDeg_comp levelLE_one_Nq levelLE_q_Nq_Nq2 (levelLE_N_Nq2 (1 * q) (by simp)),
    ← iDeg_comp levelLE_q_Nq levelLE_q_Nq_Nq2 (levelLE_N_Nq2 (q * q) dvd_rfl)] at h
  rw [iDeg'_congr_d (one_mul 1).symm h1 (levelLE_N_Nq2 (1 * 1) (by simp)),
    iDeg'_congr_d (one_mul q).symm hq' (levelLE_N_Nq2 (1 * q) (by simp)),
    iDeg'_congr_d (pow_two q) hq2 (levelLE_N_Nq2 (q * q) dvd_rfl)]
  exact h

end Levels

section TwoLevels

theorem heckeT_smul (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ]
    (r : 𝒪) (x : H1 M H 𝒪) : heckeT M H ℓ 𝒪 (r • x) = r • heckeT M H ℓ 𝒪 x :=
  (heckeTL M H 𝒪 ℓ).map_smul r x

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
  (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
  (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
  (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
  (S : Set ℕ) (hqS : q ∈ S) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen N S,
      opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g)
  (hcomm' : ∀ g g' : Gen (N * q ^ 2) S,
      opFamily (N * q ^ 2) ⊤ S 𝒪 g * opFamily (N * q ^ 2) ⊤ S 𝒪 g' =
        opFamily (N * q ^ 2) ⊤ S 𝒪 g' * opFamily (N * q ^ 2) ⊤ S 𝒪 g)
  (θbar : Gen N S → k) (θbar' : Gen (N * q ^ 2) S → k)

local notation3 "𝕋" => (CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra
local notation3 "𝕋'" => (CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra

include hq in

theorem not_dvd_mul_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓN : ¬ ℓ ∣ N) : ¬ ℓ ∣ N * q ^ 2 := by
  intro h
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
  · exact hℓN h
  · exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h))

include hq in
theorem eq_of_dvd_mul_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) : q = ℓ := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hℓM with h | h
  · exact absurd h hℓN
  · exact ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h)).symm

noncomputable def τ : Gen (N * q ^ 2) S → ↥𝕋
  | .T ℓ hℓ hℓS hℓM => gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS (fun h => hℓM (h.mul_right _)))
  | .U ℓ hℓ _ => if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0
  | .dia _ => 1

theorem τ_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓM) = gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓN) := rfl

theorem τ_U_of_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.U ℓ hℓ hℓM) = gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ hℓN) := by
  show (if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0) = _
  rw [dif_pos hℓN]

theorem τ_U_of_not_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.U ℓ hℓ hℓM) = 0 := by
  show (if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0) = _
  rw [dif_neg hℓN]

theorem τ_dia (d : (ZMod (N * q ^ 2))ˣ) : τ N q S 𝒪 k hcomm θbar (.dia d) = 1 := rfl

noncomputable def ψ : MvPolynomial (Gen (N * q ^ 2) S) 𝒪 →ₐ[𝒪] ↥𝕋 :=
  MvPolynomial.aeval (τ N q S 𝒪 k hcomm θbar)

theorem ψ_X (g : Gen (N * q ^ 2) S) :
    ψ N q S 𝒪 k hcomm θbar (MvPolynomial.X g) = τ N q S 𝒪 k hcomm θbar g := by
  simp [ψ]

theorem ψ_C (r : 𝒪) : ψ N q S 𝒪 k hcomm θbar (MvPolynomial.C r) = algebraMap 𝒪 ↥𝕋 r :=
  MvPolynomial.aeval_C _ r

include hq hqS in
theorem ψ_surjective : Function.Surjective (ψ N q S 𝒪 k hcomm θbar) := by
  refine surjective_of_forall_gOp_mem_range N S 𝒪 k hcomm θbar _ fun g => ?_
  cases g with
  | T ℓ hℓ hℓS hℓN =>
    have hℓq : ℓ ≠ q := fun h => hℓS (h ▸ hqS)
    exact ⟨MvPolynomial.X (Gen.T ℓ hℓ hℓS (not_dvd_mul_sq N q hq hℓ hℓq hℓN)), by
      rw [ψ_X, τ_T N q S 𝒪 k hcomm θbar ℓ hℓ hℓS _ hℓN]⟩
  | U ℓ hℓ hℓN =>
    exact ⟨MvPolynomial.X (Gen.U ℓ hℓ (hℓN.mul_right _)), by
      rw [ψ_X, τ_U_of_dvd N q S 𝒪 k hcomm θbar ℓ hℓ _ hℓN]⟩
  | dia d =>
    exact ⟨1, by rw [map_one, gOp_dia_eq_one]⟩

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
  (hπk : ∀ g : Gen N S, πk (Sp.toCornerRing i₀
    ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
  (Sp' : IharaLemma.IdempotentSplitting
    ↥(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra)
  (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k)
  (hπk' : ∀ g : Gen (N * q ^ 2) S, πk' (Sp'.toCornerRing i₀'
    ⟨(hdata (N * q ^ 2) ⊤ S 𝒪 k hcomm' θbar').op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
      θbar' g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2)))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N),
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)) = 0)

include hπk in
theorem hπk_gOp (g : Gen N S) : πk (Sp.toCornerRing i₀ (gOp N S 𝒪 k hcomm θbar g)) = θbar g := hπk g

include hπk' in
theorem hπk'_gOp (g : Gen (N * q ^ 2) S) :
    πk' (Sp'.toCornerRing i₀' (gOp (N * q ^ 2) S 𝒪 k hcomm' θbar' g)) = θbar' g := hπk' g

set_option maxHeartbeats 16000000 in
include hq hπk hπk' hθT hθU hθq in

theorem πk_τ_eq (g : Gen (N * q ^ 2) S) :
    πk (Sp.toCornerRing i₀ (τ N q S 𝒪 k hcomm θbar g)) = θbar' g := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    rw [τ_T N q S 𝒪 k hcomm θbar ℓ hℓ hℓS hℓM (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2))),
      hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk, hθT]
  | U ℓ hℓ hℓM =>
    by_cases h : ℓ ∣ N
    · rw [τ_U_of_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk,
        hθU ℓ hℓ hℓM h]
    · have hz : θbar' (Gen.U ℓ hℓ hℓM) = 0 := by
        have key : ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓM' : ℓ' ∣ N * q ^ 2), q = ℓ' →
            θbar' (Gen.U ℓ' hℓ' hℓM') = 0 := by
          rintro ℓ' hℓ' hℓM' rfl
          exact hθq
        exact key ℓ hℓ hℓM (eq_of_dvd_mul_sq N q hq hℓ hℓM h)
      rw [τ_U_of_not_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, RingHom.map_zero, map_zero, hz]
  | dia d =>
    have h' := hπk'_gOp N q S 𝒪 k hcomm' θbar' Sp' i₀' πk' hπk' (Gen.dia d)
    rw [gOp_dia_eq_one (N * q ^ 2) S 𝒪 k hcomm' θbar' d, RingHom.map_one, map_one] at h'
    rw [τ_dia, RingHom.map_one, map_one, h']

set_option maxHeartbeats 16000000 in
include hq hπk hπk' hθT hθU hθq in

theorem comap_eq (hk : Function.Surjective (algebraMap 𝒪 k)) :
    (Sp.𝔪 i₀).comap (ψ N q S 𝒪 k hcomm θbar).toRingHom =
      (Sp'.𝔪 i₀').comap (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar').toRingHom := by
  have H : (Sp.𝔪 i₀).comap (ψ N q S 𝒪 k hcomm θbar) =
      (Sp'.𝔪 i₀').comap (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar') := by
    rw [comap_𝔪_eq_ker_aeval N S 𝒪 k hcomm θbar Sp i₀ πk hk,
      comap_𝔪_eq_ker_aeval (N * q ^ 2) S 𝒪 k hcomm' θbar' Sp' i₀' πk' hk]
    have hfg : (fun g => πk (Sp.toCornerRing i₀ (ψ N q S 𝒪 k hcomm θbar (MvPolynomial.X g)))) =
        (fun g => πk' (Sp'.toCornerRing i₀'
          (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar' (MvPolynomial.X g)))) := by
      funext g
      rw [ψ_X, freeToT_X,
        πk_τ_eq N q hq S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq,
        hπk'_gOp N q S 𝒪 k hcomm' θbar' Sp' i₀' πk' hπk']
    rw [hfg]
  ext f
  exact SetLike.ext_iff.mp H f

noncomputable def wL : H1 N ⊤ 𝒪 →ₗ[𝒪] H1 (N * q ^ 2) ⊤ 𝒪 :=
  (q : 𝒪) • iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
    - (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (heckeTL N ⊤ 𝒪 q)
    + iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2

theorem wL_apply (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 v = (q : 𝒪) • iDeg' N (N * q ^ 2) ⊤ ⊤ 1 𝒪 h1 v
      - iDeg' N (N * q ^ 2) ⊤ ⊤ q 𝒪 hq' (heckeT N ⊤ q 𝒪 v)
      + iDeg' N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 hq2 v := rfl

include hq hqN in

theorem wL_τ_smul (g : Gen (N * q ^ 2) S) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 ((τ N q S 𝒪 k hcomm θbar g) • v) =
      (gOp (N * q ^ 2) S 𝒪 k hcomm' θbar' g) • wL N q h1 hq' hq2 𝒪 v := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓq : ℓ ≠ q := fun h => hℓM (h ▸ dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)
    have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
    show wL N q h1 hq' hq2 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (wL N q h1 hq' hq2 𝒪 v)
    rw [wL_apply, wL_apply, map_add, map_sub, heckeT_smul,
      heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
      iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓM,
      iDeg_heckeT_comm_of_coprime hq' hcop hℓ hℓM,
      iDeg_heckeT_comm_of_coprime hq2 (Nat.Coprime.pow_right 2 hcop) hℓ hℓM]
  | U ℓ hℓ hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    by_cases h : ℓ ∣ N
    · have hℓq : ℓ ≠ q := fun h' => hqN (h' ▸ h)
      have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
      rw [τ_U_of_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h]
      show wL N q h1 hq' hq2 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (wL N q h1 hq' hq2 𝒪 v)
      rw [wL_apply, wL_apply, map_add, map_sub, heckeT_smul,
        heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
        iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right ℓ) h,
        iDeg_heckeT_comm_of_dvd hq' hcop h,
        iDeg_heckeT_comm_of_dvd hq2 (Nat.Coprime.pow_right 2 hcop) h]
    · have key : ∀ (ℓ' : ℕ) (_ : NeZero ℓ'), q = ℓ' →
          heckeT (N * q ^ 2) ⊤ ℓ' 𝒪 (wL N q h1 hq' hq2 𝒪 v) = 0 := by
        rintro ℓ' _ rfl
        rw [wL_apply, Nat.cast_smul_eq_nsmul, heckeT_levelRaisingComb_eq_zero hq hqN h1 hq' hq2 v]
      rw [τ_U_of_not_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, zero_smul, map_zero]
      exact (key ℓ inferInstance (eq_of_dvd_mul_sq N q hq hℓ hℓM h)).symm
  | dia d =>
    rw [gOp_dia_smul]
    show wL N q h1 hq' hq2 𝒪 ((1 : ↥𝕋) • v) = _
    rw [one_smul]

set_option maxHeartbeats 16000000 in
include hq hqN in

theorem wL_ψ_smul (f : MvPolynomial (Gen (N * q ^ 2) S) 𝒪) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 ((ψ N q S 𝒪 k hcomm θbar f) • v) =
      (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar' f) • wL N q h1 hq' hq2 𝒪 v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C r =>
    rw [ψ_C, freeToT_C, algebraMap_smul_eq, algebraMap_smul_eq, LinearMap.map_smul]
  | add p p' hp hp' =>
    rw [map_add, map_add, add_smul, add_smul, LinearMap.map_add, hp, hp']
  | mul_X p g hp =>
    rw [map_mul, map_mul, ψ_X, freeToT_X, subalg_smul_def, Subalgebra.coe_mul, Module.End.mul_apply,
      ← subalg_smul_def, ← subalg_smul_def, hp, wL_τ_smul N q hq hqN, subalg_smul_def,
      subalg_smul_def _ _ _ _ _ _ (_ * _), Subalgebra.coe_mul, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 16000000 in
include hq hqN hqS hπk hπk' hθT hθU hθq in

theorem wL_mem_cornerSubmodule (hk : Function.Surjective (algebraMap 𝒪 k)) (φ : H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀)) :
    wL N q h1 hq' hq2 𝒪 φ ∈ IharaLemma.cornerSubmodule (M := H1 (N * q ^ 2) ⊤ 𝒪) (Sp'.e i₀') :=
  map_mem_cornerSubmodule_of_comap_eq Sp Sp' (ψ N q S 𝒪 k hcomm θbar).toRingHom
    (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar').toRingHom
    (ψ_surjective N q hq S hqS 𝒪 k hcomm θbar) (freeToT_surjective (N * q ^ 2) S 𝒪 k hcomm' θbar')
    i₀ i₀' (comap_eq N q hq S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq hk)
    (wL N q h1 hq' hq2 𝒪).toAddMonoidHom
    (fun f v => wL_ψ_smul N q hq hqN h1 hq' hq2 S 𝒪 k hcomm hcomm' θbar θbar' f v) φ hφ

end TwoLevels

end LevelRaisingCornerSol
p2m_reactivate "P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime.LevelRaisingCornerSol"

set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (S : Set ℕ) (hqS : q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 g' =
        CohCarrier.opFamily N ⊤ S 𝒪 g' * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (hcomm' : ∀ g g' : CohCarrier.Gen (N * q ^ 2) S,
      CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (θbar' : CohCarrier.Gen (N * q ^ 2) S → IsLocalRing.ResidueField 𝒪)

    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2),
      θbar' (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) =
        θbar (CohCarrier.Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2)))))
    (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N),
      θbar' (CohCarrier.Gen.U ℓ hℓ hℓM) = θbar (CohCarrier.Gen.U ℓ hℓ hℓN))
    (hθq : θbar' (CohCarrier.Gen.U q hq (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)) = 0)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : CohCarrier.Gen (N * q ^ 2) S, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g)
    (φ : CohCarrier.H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) :
    ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
        - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
        + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ ∈
      IharaLemma.cornerSubmodule (M := CohCarrier.H1 (N * q ^ 2) ⊤ 𝒪) (Sp'.e i₀') :=
  LevelRaisingCornerSol.wL_mem_cornerSubmodule N q hq hqN h1 hq' hq2 S hqS 𝒪
    (IsLocalRing.ResidueField 𝒪) hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq
    IsLocalRing.residue_surjective φ hφ

end
p2m_reactivate "P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime.LevelRaisingCornerSol"

end S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime
end P2MW
export P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime (solution)
