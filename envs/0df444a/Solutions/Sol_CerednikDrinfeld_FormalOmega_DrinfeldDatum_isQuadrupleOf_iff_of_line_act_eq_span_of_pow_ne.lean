-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_act_eq_span_of_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/05c08471-e5d6-5ead-90e6-19de66672021

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex
import Theorems.Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le
import Theorems.Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff
import Theorems.Thm_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_act_eq_span_of_pow_ne

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace B25A

section Iota

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

noncomputable def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (N : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N :=
  { toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
    map_add' := fun a b => map_add _ a b
    map_smul' := fun b p => by
      rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rfl }

theorem ιB_apply (N : FullLattice 𝒪 K) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p = LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap p := rfl

theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) : ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

end Iota

section Sat

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem mem_smul_top_of_smul_mem {L : Type} [AddCommGroup L] [Module B L] [Module.Invertible B L]
    (x : PrimeSpectrum B) {s : B} (hs : s ∉ x.asIdeal) {l : L} (h : s • l ∈ (x.asIdeal • ⊤ : Submodule B L)) :
    l ∈ (x.asIdeal • ⊤ : Submodule B L) := by
  rw [← Submodule.Quotient.mk_eq_zero, ← (TensorProduct.quotTensorEquivQuotSMul L x.asIdeal).symm.map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have h1 : (1 : B ⧸ x.asIdeal) ⊗ₜ[B] (s • l) = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    exact h
  have h2 : (Ideal.Quotient.mk x.asIdeal s) • ((1 : B ⧸ x.asIdeal) ⊗ₜ[B] l) = 0 := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← h1, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  have hs' : Ideal.Quotient.mk x.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  haveI : Module.IsTorsionFree (B ⧸ x.asIdeal) ((B ⧸ x.asIdeal) ⊗[B] L) := Module.Flat.isTorsionFree
  exact (smul_eq_zero_iff_right hs').mp h2

theorem mem_line_sup_of_smul_mem (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) (x : PrimeSpectrum B)
    {s : B} (hs : s ∉ x.asIdeal) {p : latticeBaseChange 𝒪 K B M}
    (h : s • p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  haveI := d.invertible M
  have key : ∀ q : latticeBaseChange 𝒪 K B M,
      q ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) ↔
        (d.line M).mkQ q ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ d.line M)) := by
    intro q
    rw [← Submodule.range_mkQ (d.line M), LinearMap.range_eq_map, ← Submodule.map_smul'', ← Submodule.mem_comap,
      Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]
  rw [key] at h ⊢
  rw [map_smul] at h
  exact mem_smul_top_of_smul_mem x hs h

end Sat

end B25A

namespace B25A

section Core

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem map_mem_smul_top {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module B T']
    (P : T →ₗ[B] T') (x : PrimeSpectrum B) (h : LinearMap.range P ≤ x.asIdeal • (⊤ : Submodule B T'))
    (m : stalk B x T) :
    LocalizedModule.map x.asIdeal.primeCompl P m ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
  have closed : ∀ (c : locRing B x) (n : stalk B x T'), n ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) →
      c • n ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
    intro c n hn
    induction hn using Submodule.smul_induction_on' with
    | smul r hr n _ => rw [smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    | add a _ b _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [LocalizedModule.map_mk]
    have e : LocalizedModule.mk (P t) s = Localization.mk 1 s • LocalizedModule.mk (P t) (1 : x.asIdeal.primeCompl) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [e]
    apply closed
    have aux : ∀ n : T', n ∈ x.asIdeal • (⊤ : Submodule B T') →
        LocalizedModule.mk n (1 : x.asIdeal.primeCompl) ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
      intro n hn
      induction hn using Submodule.smul_induction_on' with
      | smul r hr n _ =>
        rw [← LocalizedModule.smul'_mk]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      | add a _ b _ ha hb =>
        rw [show LocalizedModule.mk (a + b) (1 : x.asIdeal.primeCompl) = LocalizedModule.mk a 1 + LocalizedModule.mk b 1 from
          (map_add (LocalizedModule.mkLinearMap x.asIdeal.primeCompl T') a b)]
        exact Submodule.add_mem _ ha hb
    exact aux _ (h ⟨t, rfl⟩)

theorem exists_smul_eq_ιB (M : FullLattice 𝒪 K) (x : PrimeSpectrum B) (D : Submodule B (latticeBaseChange 𝒪 K B M))
    (m : latticeBaseChange 𝒪 K (locRing B x) M)
    (hm : m ∈ (lineBaseChange (toLocRing B x) M D).restrictScalars B ⊔
      (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M))) :
    ∃ s : B, s ∉ x.asIdeal ∧ ∃ p ∈ D ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      s • m = ιB (locRing B x) M p := by
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B x) x.asIdeal.primeCompl M
  obtain ⟨ℓ, hℓ, q, hq, rfl⟩ := Submodule.mem_sup.mp hm

  have Hℓ : ∀ ℓ' ∈ lineBaseChange (toLocRing B x) M D, ∃ s : B, s ∉ x.asIdeal ∧ ∃ p ∈ D, s • ℓ' = ιB (locRing B x) M p := by
    intro ℓ' hℓ'
    induction hℓ' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨1, fun h1 => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), p, hp, by rw [one_smul]; rfl⟩
    | zero => exact ⟨1, fun h1 => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), 0, D.zero_mem, by simp⟩
    | add y _ z _ hy hz =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨t, ht, p', hp', htp⟩ := hz
      refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
        D.add_mem (D.smul_mem _ hp) (D.smul_mem _ hp'), ?_⟩
      rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]
    | smul c y _ hy =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨⟨b, t⟩, hc⟩ := IsLocalization.surj x.asIdeal.primeCompl c
      dsimp only at hc
      refine ⟨t * s, fun h => (x.isPrime.mem_or_mem h).elim t.2 hs, b • p, D.smul_mem _ hp, ?_⟩
      rw [map_smul, ← hsp, smul_smul, ← algebraMap_smul (locRing B x) (↑t * s), map_mul, smul_smul,
        show algebraMap B (locRing B x) ↑t * algebraMap B (locRing B x) s * c = algebraMap B (locRing B x) (b * s) by
          rw [mul_right_comm, mul_comm _ c, hc, ← map_mul],
        algebraMap_smul]

  have Hq : ∀ q' ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M)),
      ∃ s : B, s ∉ x.asIdeal ∧ ∃ p ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
        s • q' = ιB (locRing B x) M p := by
    intro q' hq'
    induction hq' using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      obtain ⟨⟨p, s⟩, hsp⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl (ιB (locRing B x) M) n
      refine ⟨s, s.2, r • p, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
      rw [smul_comm, ← Submonoid.smul_def, hsp, map_smul]
    | add y _ z _ hy hz =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨t, ht, p', hp', htp⟩ := hz
      refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
        Submodule.add_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hp'), ?_⟩
      rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]
  obtain ⟨s, hs, p, hp, hsp⟩ := Hℓ ℓ hℓ
  obtain ⟨t, ht, p', hp', htp⟩ := Hq q hq
  refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
    Submodule.add_mem _ (Submodule.mem_sup_left (D.smul_mem _ hp)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hp')), ?_⟩
  rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]

theorem tmul_mem_line_sup_of_apply_mem (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) (x : PrimeSpectrum B)
    {T : Type} [AddCommGroup T] [Module B T]
    (u : latticeBaseChange 𝒪 K (locRing B x) M →ₗ[locRing B x] stalk B x T) (hu : Function.Surjective u)
    (hker : LinearMap.ker u = (d.map π (toLocRing B x)).line M) (p : ↥M.1)
    (hp : u ((1 : locRing B x) ⊗ₜ[𝒪] p) ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T))) :
    (1 : B) ⊗ₜ[𝒪] p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B x) x.asIdeal.primeCompl M

  have hsurj : Function.Surjective (u.restrictScalars B) := hu
  have himg : (x.asIdeal • ⊤ : Submodule B (stalk B x T)) =
      ((x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M))).map (u.restrictScalars B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  rw [himg] at hp
  obtain ⟨q, hq, hqe⟩ := hp
  have hk : (1 : locRing B x) ⊗ₜ[𝒪] p - q ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hqe.symm
  rw [hker] at hk
  have hm : (1 : locRing B x) ⊗ₜ[𝒪] p ∈ (lineBaseChange (toLocRing B x) M (d.line M)).restrictScalars B ⊔
      (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M)) := by
    have : (1 : locRing B x) ⊗ₜ[𝒪] p = ((1 : locRing B x) ⊗ₜ[𝒪] p - q) + q := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hk) (Submodule.mem_sup_right hq)
  obtain ⟨s, hs, p', hp', hsp⟩ := exists_smul_eq_ιB M x (d.line M) _ hm
  rw [← ιB_one_tmul (B := B) (A := locRing B x) M p, ← map_smul, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl (ιB (locRing B x) M)] at hsp
  obtain ⟨c, hc⟩ := hsp
  rw [smul_sub, sub_eq_zero, Submonoid.smul_def, Submonoid.smul_def, smul_smul] at hc
  apply mem_line_sup_of_smul_mem d M x (s := ↑c * s) (fun h => (x.isPrime.mem_or_mem h).elim (fun h1 => c.2 h1) hs)
  rw [← hc]
  exact Submodule.smul_mem _ _ hp'

end Core

end B25A

namespace B25A

section Quad

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem inclBaseChange_one_tmul (A : Type) [CommRing A] [Algebra 𝒪 A] {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1)
    (v : ↥M'.1) : inclBaseChange A h ((1 : A) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] (⟨(v : Fin 2 → K), h v.2⟩ : ↥M.1) := by
  unfold inclBaseChange
  rw [LinearMap.baseChange_tmul]
  rfl

theorem smulInto_baseChange_one_tmul (A : Type) [CommRing A] [Algebra 𝒪 A] {N N' : Submodule 𝒪 (Fin 2 → K)}
    (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') (v : ↥N) :
    (smulInto π h).baseChange A ((1 : A) ⊗ₜ[𝒪] v) =
      (1 : A) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • (v : Fin 2 → K), h v v.2⟩ : ↥N') := by
  rw [LinearMap.baseChange_tmul]
  rfl

theorem tmul_mem_line_L₁_sup (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
    (x : PrimeSpectrum B) (hx : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁))
    (v : Fin 2 → K) (hv : v ∈ Q.N₀ x) :
    (1 : B) ⊗ₜ[𝒪] (⟨v, Q.le x hv⟩ : ↥(Q.N₁ x)) ∈
      d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x))) := by
  apply tmul_mem_line_sup_of_apply_mem d (Q.L₁ x) x (Q.u₁ x) (Q.u₁_surjective x) (hQ x).2.2
  have h1 := Q.u₁_incl x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x)))
  rw [inclBaseChange_one_tmul] at h1
  rw [h1]
  exact map_mem_smul_top Q.Pi₀ x hx _

theorem tmul_smul_mem_line_L₀_sup (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (hQ : Q.IsQuadrupleOf d) (x : PrimeSpectrum B) (hx : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀))
    (w : Fin 2 → K) (hw : w ∈ Q.N₁ x) :
    (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • w, Q.smul_le x w hw⟩ : ↥(Q.N₀ x)) ∈
      d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))) := by
  apply tmul_mem_line_sup_of_apply_mem d (Q.L₀ x) x (Q.u₀ x) (Q.u₀_surjective x) (hQ x).2.1
  have h1 := Q.u₀_smul x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥(Q.N₁ x)))
  rw [smulInto_baseChange_one_tmul] at h1
  rw [h1]
  exact map_mem_smul_top Q.Pi₁ x hx _

end Quad

end B25A

namespace B25A

section Lattice

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

theorem latticeMap_scalarGL_comm (c c' : Kˣ) (N : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL c') N) = latticeMap (scalarGL c') (latticeMap (scalarGL c) N) := by
  rw [← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul, ← scalarGL_mul, mul_comm]

theorem latticeMap_scalarGL_inv_mul (c c' : Kˣ) (N : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (c⁻¹ * c')) (latticeMap (scalarGL c) N) = latticeMap (scalarGL c') N := by
  rw [← latticeMap_mul, ← scalarGL_mul, mul_assoc, mul_comm c' c, ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_latticeMap_scalarGL_of_forall {N₀ N₁ : Submodule 𝒪 (Fin 2 → K)} (c : Kˣ)
    (h1 : ∀ v ∈ N₀, ∃ w ∈ N₁, v = (c : K) • w) (h2 : ∀ w ∈ N₁, (c : K) • w ∈ N₀) :
    N₀ = latticeMap (scalarGL c) N₁ := by
  ext v
  rw [mem_latticeMap_scalarGL]
  constructor
  · intro hv; obtain ⟨w, hw, rfl⟩ := h1 v hv; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact h2 w hw

end Lattice

section Types

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem algebraMap_ne_zero (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 := fun h =>
  hπ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)

noncomputable def πu (hπ : Irreducible π) : Kˣ := Units.mk0 (algebraMap 𝒪 K π) (algebraMap_ne_zero (K := K) hπ)

theorem coe_πu (hπ : Irreducible π) : ((πu (K := K) hπ : Kˣ) : K) = algebraMap 𝒪 K π := rfl

variable (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
  (x : PrimeSpectrum B) (hπx : algebraMap 𝒪 B π ∈ x.asIdeal)

include hπx in

theorem stratum_cover :
    LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁) ∨ LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀) := by
  have hfg : Q.Pi₁ ∘ₗ Q.Pi₀ = algebraMap 𝒪 B π • LinearMap.id := LinearMap.ext fun t => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Q.Pi₁_Pi₀]
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul Q.Pi₀ Q.Pi₁ _ hfg x hπx

theorem N₀_eq_of_not_S₁ (hS1 : ¬ LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀)) :
    Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x) := by
  have hbij := Module.Invertible.bijective_localizedModule_map_of_not_range_le Q.Pi₁ x hS1
  apply eq_latticeMap_scalarGL_of_forall
  · intro v hv
    obtain ⟨w, hw, hvw⟩ := Q.injective₀ x ⟨v, hv⟩ (Submodule.mem_sup_left (by
      rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hbij.2]; trivial))
    exact ⟨w, hw, hvw⟩
  · intro w hw; exact Q.smul_le x w hw

theorem N₀_eq_of_not_S₀ (hS0 : ¬ LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁)) :
    Q.N₀ x = Q.N₁ x := by
  have hbij := Module.Invertible.bijective_localizedModule_map_of_not_range_le Q.Pi₀ x hS0
  refine le_antisymm (Q.le x) fun v hv => ?_
  exact Q.injective₁ x ⟨v, hv⟩ (Submodule.mem_sup_left (by
    rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hbij.2]; trivial))

include hQ in
theorem clause₃ (v : ↥(Q.N₁ x)) (hv : (v : Fin 2 → K) ∉ Q.N₀ x) :
    (1 : B) ⊗ₜ[𝒪] v ∉ d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x))) :=
  (hQ x).1.2.2.1 v hv

include hQ in
theorem clause₄ (v' : ↥(Q.N₀ x)) (hv' : ¬ ∃ w : ↥(Q.N₁ x), (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) :
    (1 : B) ⊗ₜ[𝒪] v' ∉ d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))) :=
  (hQ x).1.2.2.2 v' hv'

include hQ in

theorem vertexNondegAt_L₁_of_V0 (h : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x)) :
    d.VertexNondegAt π x.asIdeal (Q.L₁ x) := by
  intro v hnot
  apply clause₃ Q d hQ x v
  intro hv0
  rw [h, mem_latticeMap_scalarGL] at hv0
  obtain ⟨w, hw, hwv⟩ := hv0
  exact hnot ⟨⟨w, hw⟩, by rw [← hwv]; rfl⟩

include hQ in

theorem vertexNondegAt_L₀_of_V1 (h : Q.N₀ x = Q.N₁ x) : d.VertexNondegAt π x.asIdeal (Q.L₀ x) := by
  intro v' hnot
  apply clause₄ Q d hQ x v'
  rintro ⟨w, hw⟩
  exact hnot ⟨⟨w, by show (w : Fin 2 → K) ∈ Q.N₀ x; rw [h]; exact w.2⟩, hw⟩

end Types

end B25A

namespace B25A

section Edge

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

variable (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
  (x : PrimeSpectrum B)
  (hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁))
  (hS1 : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀))

theorem not_even_one_aux {e : ℤ} (h : Even e) (he : e = 1 ∨ e = -1) : False := by
  obtain ⟨k, hk⟩ := h; rcases he with rfl | rfl <;> omega

include hπ hS0 hS1 in

theorem N₀_ne_N₁_of_E : Q.N₀ x ≠ Q.N₁ x := by
  intro h
  have h0 := Q.hasDetIndex₀ x hS0
  have h1 := Q.hasDetIndex₁ x hS1
  refine not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ (Q.N₁ x) 1 (-1) 0
    h1 (by rw [scalarGL_one, latticeMap_one, ← h]; exact h0)) (Or.inr (by norm_num))

include hπ hS0 hS1 in

theorem exists_mem_N₀_not_smul_of_E : ∃ v ∈ Q.N₀ x, ¬ ∃ w ∈ Q.N₁ x, v = algebraMap 𝒪 K π • w := by
  by_contra hne
  push_neg at hne
  have heq : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x) :=
    eq_latticeMap_scalarGL_of_forall _ (fun v hv => by
      obtain ⟨w, hw, hvw⟩ := hne v hv; exact ⟨w, hw, hvw⟩) (fun w hw => Q.smul_le x w hw)
  have h0 := Q.hasDetIndex₀ x hS0
  have h1 := Q.hasDetIndex₁ x hS1
  rw [heq] at h0
  exact not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ (Q.N₁ x) _ (-1) 0
    h1 h0) (Or.inr (by norm_num))

include hπ hQ hS0 hS1 in

theorem not_vertexNondegAt_L₁_of_E : ¬ d.VertexNondegAt π x.asIdeal (Q.L₁ x) := by
  intro hV
  obtain ⟨v, hv0, hnot⟩ := exists_mem_N₀_not_smul_of_E hπ Q x hS0 hS1
  exact hV ⟨v, Q.le x hv0⟩ (fun ⟨w, hw⟩ => hnot ⟨w, w.2, hw⟩) (tmul_mem_line_L₁_sup Q d hQ x hS0 v hv0)

include hπ hQ hS0 hS1 in

theorem not_vertexNondegAt_L₀_of_E : ¬ d.VertexNondegAt π x.asIdeal (Q.L₀ x) := by
  intro hV
  obtain ⟨w, hw1, hw0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (Q.le x) (N₀_ne_N₁_of_E hπ Q x hS0 hS1))
  refine hV ⟨algebraMap 𝒪 K π • w, Q.smul_le x w hw1⟩ ?_ (tmul_smul_mem_line_L₀_sup Q d hQ x hS1 w hw1)
  rintro ⟨w', hw'⟩
  have : w = (w' : Fin 2 → K) := smul_right_injective (Fin 2 → K) (algebraMap_ne_zero (K := K) hπ) hw'
  exact hw0 (this ▸ w'.2)

include hπ hQ hS0 hS1 in

theorem false_of_vertexNondegAt_of_E (M : FullLattice 𝒪 K) (hM : d.VertexNondegAt π x.asIdeal M) (c : Kˣ)
    (hc : latticeMap (scalarGL c) M.1 = (Q.L₀ x).1 ∨ latticeMap (scalarGL c) M.1 = (Q.L₁ x).1) : False := by
  have hVc := (CerednikDrinfeld.FormalOmega.DeligneDatum.vertexNondegAt_act_scalarGL_iff π d x.asIdeal c M).mpr hM
  rcases hc with hc | hc
  · have : FullLattice.act (scalarGL c) M = Q.L₀ x := Subtype.ext hc
    rw [this] at hVc
    exact not_vertexNondegAt_L₀_of_E hπ Q d hQ x hS0 hS1 hVc
  · have : FullLattice.act (scalarGL c) M = Q.L₁ x := Subtype.ext hc
    rw [this] at hVc
    exact not_vertexNondegAt_L₁_of_E hπ Q d hQ x hS0 hS1 hVc

include hQ in

theorem mem_N₀_of_tmul_mem (v : Fin 2 → K) (hv1 : v ∈ Q.N₁ x)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv1⟩ : ↥(Q.N₁ x)) ∈
      d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x)))) : v ∈ Q.N₀ x := by
  by_contra hv0
  exact clause₃ Q d hQ x ⟨v, hv1⟩ hv0 h

include hQ in

theorem exists_of_tmul_mem (v : Fin 2 → K) (hv0 : v ∈ Q.N₀ x)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv0⟩ : ↥(Q.N₀ x)) ∈
      d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x)))) :
    ∃ w ∈ Q.N₁ x, v = algebraMap 𝒪 K π • w := by
  by_contra hne
  push_neg at hne
  exact clause₄ Q d hQ x ⟨v, hv0⟩ (fun ⟨w, hw⟩ => hne w w.2 hw) h

end Edge

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem tmul_mem_of_eq (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B) {L L' : FullLattice 𝒪 K} (hL : L = L')
    (v : Fin 2 → K) (hv : v ∈ L.1) (hv' : v ∈ L'.1)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥L.1) ∈ d.line L ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) :
    (1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥L'.1) ∈ d.line L' ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L')) := by
  subst hL; exact h

end Transport

end B25A

namespace B25A

section Compare

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

variable (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B) (hπx : algebraMap 𝒪 B π ∈ x.asIdeal)
  (Q : DrinfeldDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
  (Q' : DrinfeldDatum (K := K) π B) (hQ' : Q'.IsQuadrupleOf d)

local notation "S0" R => LinearMap.range (DrinfeldDatum.Pi₀ R) ≤ x.asIdeal • (⊤ : Submodule B (DrinfeldDatum.T₁ R))
local notation "S1" R => LinearMap.range (DrinfeldDatum.Pi₁ R) ≤ x.asIdeal • (⊤ : Submodule B (DrinfeldDatum.T₀ R))

include hπ hπx hQ' in

theorem false_of_vertex_edge (M : FullLattice 𝒪 K) (hM : d.VertexNondegAt π x.asIdeal M)
    (hS0' : S0 Q') (hS1' : S1 Q') : False := by
  obtain ⟨c, hc⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx M (Q'.L₀ x) (Q'.L₁ x) hM (hQ' x).1
  exact false_of_vertexNondegAt_of_E hπ Q' d hQ' x hS0' hS1' M hM c hc

include hπ hπx hQ hQ' in

theorem eq_of_V0_V0 (hS0 : S0 Q) (h0 : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x))
    (hS0' : S0 Q') (h0' : Q'.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q'.N₁ x)) :
    Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  have hV := vertexNondegAt_L₁_of_V0 hπ Q d hQ x h0
  obtain ⟨c, hc⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1

  obtain ⟨c', hc'⟩ : ∃ c' : Kˣ, latticeMap (scalarGL c') (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · refine ⟨(πu (K := K) hπ)⁻¹ * c, ?_⟩
      change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hc
      rw [h0'] at hc
      rw [scalarGL_mul, latticeMap_mul, hc, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
    · exact ⟨c, hc⟩
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx0' := Q'.hasDetIndex₀ x hS0'
  have hN0' : Q'.N₀ x = latticeMap (scalarGL c') (Q.N₀ x) := by
    rw [h0', ← hc', h0, latticeMap_scalarGL_comm]
  have key : latticeMap (scalarGL c') (Q.N₀ x) = Q.N₀ x :=
    CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c' 0 idx0 (hN0' ▸ idx0')
  refine ⟨by rw [hN0', key], ?_⟩
  rw [← hc']
  apply latticeMap_injective (scalarGL (πu (K := K) hπ))
  rw [← latticeMap_scalarGL_comm, ← h0, key]

include hπ hπx hQ hQ' in

theorem eq_of_V1_V1 (hS1 : S1 Q) (h1 : Q.N₀ x = Q.N₁ x) (hS1' : S1 Q') (h1' : Q'.N₀ x = Q'.N₁ x) :
    Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  have hV := vertexNondegAt_L₀_of_V1 Q d hQ x h1
  obtain ⟨c, hc⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₀ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1
  have hc1 : latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₀ x at hc; rwa [h1, h1'] at hc
    · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₁ x at hc; rwa [h1] at hc
  have idx1 := Q.hasDetIndex₁ x hS1
  have idx1' := Q'.hasDetIndex₁ x hS1'
  have key : latticeMap (scalarGL c) (Q.N₁ x) = Q.N₁ x :=
    CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c (-1) idx1 (hc1.symm ▸ idx1')
  have hN1 : Q.N₁ x = Q'.N₁ x := by rw [← hc1, key]
  exact ⟨by rw [h1, h1', hN1], hN1⟩

include hπ hπx hQ hQ' in

theorem false_of_V0_V1 (hS0 : S0 Q) (h0 : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x))
    (hS1' : S1 Q') (h1' : Q'.N₀ x = Q'.N₁ x) : False := by
  have hV := vertexNondegAt_L₁_of_V0 hπ Q d hQ x h0
  obtain ⟨c, hc⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1
  have hc1 : latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hc; rwa [h1'] at hc
    · exact hc
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx1' := Q'.hasDetIndex₁ x hS1'
  rw [h0] at idx0
  rw [← hc1, ← latticeMap_scalarGL_inv_mul (πu (K := K) hπ) c] at idx1'
  exact not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ _ 0 (-1) idx0 idx1')
    (Or.inl (by norm_num))

include hπ hQ hQ' in

theorem N₁_le_of_E_E (hS1 : S1 Q) (hN0 : Q.N₀ x = Q'.N₀ x) : Q.N₁ x ≤ Q'.N₁ x := by
  intro w hw
  have hmem := tmul_smul_mem_line_L₀_sup Q d hQ x hS1 w hw
  have hL : Q.L₀ x = Q'.L₀ x := Subtype.ext hN0
  have hmem' := tmul_mem_of_eq d x hL _ (Q.smul_le x w hw) (by show _ ∈ Q'.N₀ x; rw [← hN0]; exact Q.smul_le x w hw) hmem
  obtain ⟨w', hw', hww'⟩ := exists_of_tmul_mem Q' d hQ' x _ _ hmem'
  have : w = w' := smul_right_injective (Fin 2 → K) (algebraMap_ne_zero (K := K) hπ) hww'
  exact this ▸ hw'

include hQ hQ' in

theorem N₀_le_of_E_E (hS0 : S0 Q) (hN1 : Q.N₁ x = Q'.N₁ x) : Q.N₀ x ≤ Q'.N₀ x := by
  intro v hv
  have hmem := tmul_mem_line_L₁_sup Q d hQ x hS0 v hv
  have hL : Q.L₁ x = Q'.L₁ x := Subtype.ext hN1
  have hmem' := tmul_mem_of_eq d x hL _ (Q.le x hv) (by show _ ∈ Q'.N₁ x; rw [← hN1]; exact Q.le x hv) hmem
  exact mem_N₀_of_tmul_mem Q' d hQ' x v _ hmem'

include hπ hπx hQ hQ' in

theorem eq_of_E_E (hS0 : S0 Q) (hS1 : S1 Q) (hS0' : S0 Q') (hS1' : S1 Q') :
    Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  obtain ⟨c, X, Y, hX, hY, hXY⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt hπ d x.asIdeal hπx
      (Q.L₀ x) (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) (hQ x).1 (hQ' x).1
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx1 := Q.hasDetIndex₁ x hS1
  have idx0' := Q'.hasDetIndex₀ x hS0'
  have idx1' := Q'.hasDetIndex₁ x hS1'
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  ·
    change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₀ x at hXY
    have key := CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c 0 idx0 (hXY.symm ▸ idx0')
    have hN0 : Q.N₀ x = Q'.N₀ x := by rw [← hXY, key]
    exact ⟨hN0, le_antisymm (N₁_le_of_E_E hπ d x Q hQ Q' hQ' hS1 hN0) (N₁_le_of_E_E hπ d x Q' hQ' Q hQ hS1' hN0.symm)⟩
  ·
    change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₁ x at hXY
    exact (not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ c 0 (-1) idx0
      (hXY.symm ▸ idx1')) (Or.inl (by norm_num))).elim
  ·
    change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hXY
    exact (not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ c (-1) 0 idx1
      (hXY.symm ▸ idx0')) (Or.inr (by norm_num))).elim
  ·
    change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x at hXY
    have key := CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c (-1) idx1 (hXY.symm ▸ idx1')
    have hN1 : Q.N₁ x = Q'.N₁ x := by rw [← hXY, key]
    exact ⟨le_antisymm (N₀_le_of_E_E d x Q hQ Q' hQ' hS0 hN1) (N₀_le_of_E_E d x Q' hQ' Q hQ hS0' hN1.symm), hN1⟩

end Compare

end B25A

namespace B25N3

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

noncomputable def intCoord (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) : ℤ_[p] :=
  ((mem_stdLattice ℤ_[p] ℚ_[p]).mp v.2 i).choose

theorem algebraMap_intCoord (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    algebraMap ℤ_[p] ℚ_[p] (intCoord p v i) = (v : Fin 2 → ℚ_[p]) i :=
  ((mem_stdLattice ℤ_[p] ℚ_[p]).mp v.2 i).choose_spec

theorem intCoord_add (v w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    intCoord p (v + w) i = intCoord p v i + intCoord p w i := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [map_add, algebraMap_intCoord, algebraMap_intCoord, algebraMap_intCoord, Submodule.coe_add, Pi.add_apply]

theorem intCoord_smul (r : ℤ_[p]) (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    intCoord p (r • v) i = r * intCoord p v i := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [map_mul, algebraMap_intCoord, algebraMap_intCoord, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

variable {κ : Type} [Field κ] [Algebra ℤ_[p] κ]

noncomputable def coordRed (i : Fin 2) : κ ⊗[ℤ_[p]] ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 →ₗ[κ] κ :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun v => b * algebraMap ℤ_[p] κ (intCoord p v i)
          map_add' := fun v w => by rw [intCoord_add, map_add, mul_add]
          map_smul' := fun r v => by
            rw [intCoord_smul, map_mul, RingHom.id_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun a b => by ext v; simp [add_mul]
      map_smul' := fun a b => by ext v; simp [mul_assoc] }

theorem coordRed_tmul (i : Fin 2) (b : κ) (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    coordRed p (κ := κ) i (b ⊗ₜ[ℤ_[p]] v) = b * algebraMap ℤ_[p] κ (intCoord p v i) :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ b v

theorem intCoord_stdBasisVec (i j : Fin 2) :
    intCoord p (stdBasisVec ℚ_[p] j) i = if i = j then 1 else 0 := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [algebraMap_intCoord]
  show (Pi.single j (1 : ℚ_[p]) : Fin 2 → ℚ_[p]) i = _
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp [h]

end B25N3

namespace B25N3

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem algebraMap_p_eq_zero : algebraMap ℤ_[p] κ (p : ℤ_[p]) = 0 := by
  rw [map_natCast]; exact CharP.cast_eq_zero κ p

theorem algebraMap_pow_p (a : ℤ_[p]) : (algebraMap ℤ_[p] κ a) ^ p = algebraMap ℤ_[p] κ a := by
  have hmem : a ^ p - a ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card,
      sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  have : algebraMap ℤ_[p] κ (a ^ p - a) = 0 := by rw [← hb, map_mul, algebraMap_p_eq_zero, mul_zero]
  rwa [map_sub, map_pow, sub_eq_zero] at this

theorem dvd_of_algebraMap_eq_zero {a : ℤ_[p]} (ha : algebraMap ℤ_[p] κ a = 0) : (p : ℤ_[p]) ∣ a := by
  have hker : RingHom.ker (algebraMap ℤ_[p] κ) ≠ ⊤ := RingHom.ker_ne_top _
  have hle := IsLocalRing.le_maximalIdeal hker
  have : a ∈ IsLocalRing.maximalIdeal ℤ_[p] := hle ((RingHom.mem_ker).mpr ha)
  rw [PadicInt.maximalIdeal_eq_span_p] at this
  exact Ideal.mem_span_singleton.mp this

theorem one_tmul_not_mem_span (c : κ) (hc : c ^ p ≠ c) (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (hw : ¬ ∀ i, (p : ℤ_[p]) ∣ intCoord p w i) :
    (1 : κ) ⊗ₜ[ℤ_[p]] w ∉ Submodule.span κ
      {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} := by
  intro h
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp h
  have g0 : coordRed p (κ := κ) 0 (c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = c := by
    rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]
    simp
  have g1 : coordRed p (κ := κ) 1 (c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = 1 := by
    rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]
    simp
  have e0 : l * c = algebraMap ℤ_[p] κ (intCoord p w 0) := by
    have := congrArg (coordRed p (κ := κ) 0) hl
    rwa [map_smul, g0, coordRed_tmul, one_mul, smul_eq_mul] at this
  have e1 : l = algebraMap ℤ_[p] κ (intCoord p w 1) := by
    have := congrArg (coordRed p (κ := κ) 1) hl
    rwa [map_smul, g1, coordRed_tmul, one_mul, smul_eq_mul, mul_one] at this
  have h0 := algebraMap_pow_p p (κ := κ) (intCoord p w 0)
  have h1 := algebraMap_pow_p p (κ := κ) (intCoord p w 1)
  rw [← e0, mul_pow] at h0
  rw [← e1] at h1
  rw [h1] at h0

  have hl0 : l = 0 := by
    by_contra hne
    exact hc (mul_left_cancel₀ hne h0)
  have d0 : (p : ℤ_[p]) ∣ intCoord p w 0 := dvd_of_algebraMap_eq_zero p (κ := κ) (by rw [← e0, hl0, zero_mul])
  have d1 : (p : ℤ_[p]) ∣ intCoord p w 1 := dvd_of_algebraMap_eq_zero p (κ := κ) (by rw [← e1, hl0])
  exact hw (fun i => by fin_cases i <;> first | exact d0 | exact d1)

end B25N3

namespace B25N3

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev pu : ℚ_[p]ˣ := unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero

theorem coe_pu : ((pu p : ℚ_[p]ˣ) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) := unitOfNeZero_coe _

noncomputable abbrev Lone : FullLattice ℤ_[p] ℚ_[p] := FullLattice.act (scalarGL (pu p)⁻¹) (stdFullLattice ℚ_[p])

theorem mem_Lone_iff (v : Fin 2 → ℚ_[p]) :
    v ∈ (Lone p).1 ↔ algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ stdLattice ℤ_[p] ℚ_[p] := by
  show v ∈ latticeMap (scalarGL (pu p)⁻¹) (stdLattice ℤ_[p] ℚ_[p]) ↔ _
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (pu p).ne_zero, one_smul]
  · intro hv
    exact ⟨_, hv, by rw [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (pu p).ne_zero, one_smul]⟩

theorem std_le_Lone : (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 ≤ (Lone p).1 := by
  intro v hv
  rw [mem_Lone_iff]
  exact (stdLattice ℤ_[p] ℚ_[p]).smul_mem _ hv

theorem smul_mem_std_of_mem_Lone (v : Fin 2 → ℚ_[p]) (hv : v ∈ (Lone p).1) :
    algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 :=
  (mem_Lone_iff p v).mp hv

theorem exists_eq_smul_of_dvd (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (h : ∀ i, (p : ℤ_[p]) ∣ intCoord p w i) :
    ∃ w' : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1,
      (w : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • (w' : Fin 2 → ℚ_[p]) := by
  choose b hb using h
  refine ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (b i), fun i => ⟨b i, rfl⟩⟩, ?_⟩
  funext i
  rw [Pi.smul_apply, smul_eq_mul, ← map_mul, ← hb, algebraMap_intCoord]

variable {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem asIdeal_eq_bot (x : PrimeSpectrum κ) : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal

theorem vertexNondegAt_std (c : κ) (hc : c ^ p ≠ c) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (x : PrimeSpectrum κ) : d.VertexNondegAt (p : ℤ_[p]) x.asIdeal (stdFullLattice ℚ_[p]) := by
  intro v hv hmem
  rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq, hd] at hmem
  refine one_tmul_not_mem_span p c hc v ?_ hmem
  intro hall
  obtain ⟨w', hw'⟩ := exists_eq_smul_of_dvd p v hall
  exact hv ⟨w', hw'⟩

theorem edgeNondegAt_std_Lone (c : κ) (hc : c ^ p ≠ c) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (x : PrimeSpectrum κ) : d.EdgeNondegAt (p : ℤ_[p]) x.asIdeal (stdFullLattice ℚ_[p]) (Lone p) := by
  refine ⟨std_le_Lone p, fun v => smul_mem_std_of_mem_Lone p v v.2, ?_, ?_⟩
  · intro v hv hmem
    rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq, d.homothety, hd, Submodule.map_span,
      Set.image_singleton] at hmem

    set w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 := ⟨_, smul_mem_std_of_mem_Lone p v v.2⟩ with hw
    have hvw : (latticeMapEquiv (scalarGL (pu p)⁻¹) (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 w :
        ↥(Lone p).1) = v := by
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
      show (((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • (v : Fin 2 → ℚ_[p])) = v
      rw [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (pu p).ne_zero, one_smul]
    have h1 : (1 : κ) ⊗ₜ[ℤ_[p]] v =
        actBaseChange κ (scalarGL (pu p)⁻¹) (stdFullLattice ℚ_[p]) ((1 : κ) ⊗ₜ[ℤ_[p]] w) := by
      rw [actBaseChange_tmul, hvw]; rfl
    rw [h1, ← Set.image_singleton, ← Submodule.map_span] at hmem
    obtain ⟨y, hy, hyEq⟩ := Submodule.mem_map.mp hmem
    have hy' : y = (1 : κ) ⊗ₜ[ℤ_[p]] w := (actBaseChange κ (scalarGL (pu p)⁻¹) (stdFullLattice ℚ_[p])).injective hyEq
    rw [hy'] at hy
    refine one_tmul_not_mem_span p c hc w ?_ hy
    intro hall
    obtain ⟨w', hw'⟩ := exists_eq_smul_of_dvd p w hall
    apply hv
    have : (v : Fin 2 → ℚ_[p]) = w' := by
      rw [← hvw, coe_latticeMapEquiv_apply, scalarGL_mulVec, hw', smul_smul, ← coe_pu, Units.val_inv_eq_inv_val,
        inv_mul_cancel₀ (pu p).ne_zero, one_smul]
    rw [this]; exact w'.2
  · rintro v' hnot
    exfalso
    apply hnot
    refine ⟨⟨((pu p)⁻¹ : ℚ_[p]ˣ) • (v' : Fin 2 → ℚ_[p]), mem_latticeMap_scalarGL.mpr ⟨v', v'.2, rfl⟩⟩, ?_⟩
    show (v' : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • ((((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • (v' : Fin 2 → ℚ_[p]))
    rw [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (pu p).ne_zero, one_smul]

end B25N3

namespace B25N3

section Lines

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

theorem lineBaseChange_span_singleton (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    lineBaseChange f M (Submodule.span B {y}) = Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap y} := by
  unfold lineBaseChange
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [rTensor_smul_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨y, Submodule.mem_span_singleton_self _, rfl⟩)

theorem rTensor_transportEquiv (f : B →ₐ[𝒪] B') {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1)
    (y : latticeBaseChange 𝒪 K B M₁) :
    LinearMap.rTensor (↥M₂.1) f.toLinearMap (transportEquiv B h y) =
      transportEquiv B' h (LinearMap.rTensor (↥M₁.1) f.toLinearMap y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearEquiv.map_zero]
  | add a b ha hb => rw [LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, LinearEquiv.map_add, ha, hb]
  | tmul b v => rfl

end Lines

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem line_map_L₀ (c : κ) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ)
    (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    (d.map (p : ℤ_[p]) (toLocRing κ x)).line (Q.L₀ x) = Submodule.span (locRing κ x)
      {transportEquiv (locRing κ x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
        (algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} := by
  have ht := DeligneDatum.line_transport (π := (p : ℤ_[p])) d (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
  show lineBaseChange (toLocRing κ x) (Q.L₀ x) (d.line (Q.L₀ x)) = _
  rw [ht, hd, Submodule.map_span, Set.image_singleton, lineBaseChange_span_singleton]
  congr 2
  show LinearMap.rTensor _ (toLocRing κ x).toLinearMap (transportEquiv κ h₀.symm _) = _
  rw [rTensor_transportEquiv, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_one]
  rfl

theorem line_map_L₁ (c : κ) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ) (h₁ : Q.N₁ x = (Lone p).1) :
    (d.map (p : ℤ_[p]) (toLocRing κ x)).line (Q.L₁ x) = Submodule.span (locRing κ x)
      {transportEquiv (locRing κ x) (M₁ := Lone p) (M₂ := Q.L₁ x) h₁.symm
        (actBaseChange (locRing κ x) (scalarGL (pu p)⁻¹) (stdFullLattice ℚ_[p])
          (algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 +
            (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1))} := by
  have ht := DeligneDatum.line_transport (π := (p : ℤ_[p])) d (M₁ := Lone p) (M₂ := Q.L₁ x) h₁.symm
  show lineBaseChange (toLocRing κ x) (Q.L₁ x) (d.line (Q.L₁ x)) = _
  rw [ht, d.homothety, hd, Submodule.map_span, Set.image_singleton, Submodule.map_span, Set.image_singleton,
    lineBaseChange_span_singleton]
  congr 2
  show LinearMap.rTensor _ (toLocRing κ x).toLinearMap (transportEquiv κ h₁.symm (actBaseChange κ _ _ _)) = _
  rw [rTensor_transportEquiv, rTensor_actBaseChange, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]
  rfl

end B25N3

namespace B25N3

section Node

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Lg (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : FullLattice ℤ_[p] ℚ_[p] :=
  FullLattice.act (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice ℚ_[p]))

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
  (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])

include hg in
theorem g_mulVec (s : Fin 2 → ℚ_[p]) :
    Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) s = ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) * s 0, s 1] := by
  rw [hg]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

include hg in

theorem mem_act_g_iff (v : Fin 2 → ℚ_[p]) :
    v ∈ (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])).1 ↔
      ∃ s : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1,
        v = ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) * (s : Fin 2 → ℚ_[p]) 0, (s : Fin 2 → ℚ_[p]) 1] := by
  show v ∈ latticeMap g (stdLattice ℤ_[p] ℚ_[p]) ↔ _
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, g_mulVec p g hg w⟩
  · rintro ⟨s, rfl⟩; exact ⟨s, s.2, g_mulVec p g hg s⟩

include hg in

theorem mem_Lg_iff (v : Fin 2 → ℚ_[p]) :
    v ∈ (Lg p g).1 ↔ ∃ s : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1,
      v = ![(s : Fin 2 → ℚ_[p]) 0, (((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (s : Fin 2 → ℚ_[p]) 1] := by
  show v ∈ latticeMap (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])).1 ↔ _
  rw [mem_latticeMap_scalarGL]
  have hp0 : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by rw [← coe_pu]; exact (pu p).ne_zero
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_act_g_iff p g hg w).mp hw
    refine ⟨s, ?_⟩
    funext i; fin_cases i
    · simp [← coe_pu, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ (pu p).ne_zero]
    · simp
  · rintro ⟨s, rfl⟩
    refine ⟨_, (mem_act_g_iff p g hg _).mpr ⟨s, rfl⟩, ?_⟩
    funext i; fin_cases i
    · simp [← coe_pu, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ (pu p).ne_zero]
    · simp

end Node

end B25N3

namespace B25N3

section Node2

variable (p : ℕ) [Fact p.Prime]

theorem coe_eq_intCoord (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    (w : Fin 2 → ℚ_[p]) = fun i => algebraMap ℤ_[p] ℚ_[p] (intCoord p w i) := by
  funext i; rw [algebraMap_intCoord]

theorem vec_mem_std (c : Fin 2 → ℤ_[p]) :
    (fun i => algebraMap ℤ_[p] ℚ_[p] (c i)) ∈ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 := fun i => ⟨c i, rfl⟩

variable {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem one_tmul_not_mem_span_of_coordRed_eq_zero (i : Fin 2)
    (gen : κ ⊗[ℤ_[p]] ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (hgen : coordRed p (κ := κ) i gen = 0)
    (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (hw : ¬ (p : ℤ_[p]) ∣ intCoord p w i) :
    (1 : κ) ⊗ₜ[ℤ_[p]] w ∉ Submodule.span κ {gen} := by
  intro h
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp h
  have := congrArg (coordRed p (κ := κ) i) hl
  rw [map_smul, hgen, smul_zero, coordRed_tmul, one_mul] at this
  exact hw (dvd_of_algebraMap_eq_zero p (κ := κ) this.symm)

theorem coordRed_gen0 : coordRed p (κ := κ) 0
    ((0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = 0 := by
  rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]; simp

theorem coordRed_gen1 : coordRed p (κ := κ) 1
    ((1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = 0 := by
  rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]; simp

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
  (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])

include hg in
theorem std_le_Lg : (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 ≤ (Lg p g).1 := by
  intro v hv
  rw [mem_Lg_iff p g hg]
  refine ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (![intCoord p ⟨v, hv⟩ 0, (p : ℤ_[p]) * intCoord p ⟨v, hv⟩ 1] i),
    vec_mem_std p _⟩, ?_⟩
  conv_lhs => rw [show v = ((⟨v, hv⟩ : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) from rfl, coe_eq_intCoord]
  funext i; fin_cases i
  · simp
  · simp [map_mul, ← coe_pu, ← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (pu p).ne_zero]

include hg in
theorem smul_mem_std_of_mem_Lg (v : Fin 2 → ℚ_[p]) (hv : v ∈ (Lg p g).1) :
    algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 := by
  obtain ⟨s, rfl⟩ := (mem_Lg_iff p g hg v).mp hv
  intro i; fin_cases i
  · simpa using IsLocalization.isInteger_mul ⟨(p : ℤ_[p]), rfl⟩ ((mem_stdLattice ℤ_[p] ℚ_[p]).mp s.2 0)
  · simp only [Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, ← coe_pu, ← mul_assoc,
      Units.val_inv_eq_inv_val, mul_inv_cancel₀ (pu p).ne_zero, one_mul, Fin.isValue, Fin.mk_one]
    exact (mem_stdLattice ℤ_[p] ℚ_[p]).mp s.2 1

end Node2

end B25N3

namespace B25N3

section Node3

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

omit [CharP κ p] in

theorem exists_eq_act_tmul (h : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (M : FullLattice ℤ_[p] ℚ_[p])
    (v : ↥(FullLattice.act h M).1) :
    ∃ s : ↥M.1, (v : Fin 2 → ℚ_[p]) = Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) ℚ_[p]) (s : Fin 2 → ℚ_[p]) ∧
      ∀ b : κ, b ⊗ₜ[ℤ_[p]] v = actBaseChange κ h M (b ⊗ₜ[ℤ_[p]] s) := by
  obtain ⟨w, hw, hwv⟩ := (mem_latticeMap).mp v.2
  refine ⟨⟨w, hw⟩, hwv.symm, fun b => ?_⟩
  rw [actBaseChange_tmul]
  congr 1
  exact (Subtype.ext (by rw [coe_latticeMapEquiv_apply]; exact hwv)).symm

omit [CharP κ p] in
theorem mem_span_of_equiv_mem {V W : Type} [AddCommGroup V] [Module κ V] [AddCommGroup W] [Module κ W]
    (e : V ≃ₗ[κ] W) (y z : V) (h : e y ∈ Submodule.span κ {e z}) : y ∈ Submodule.span κ {z} := by
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp h
  rw [← map_smul] at hl
  rw [← e.injective hl]
  exact Submodule.mem_span_singleton.mpr ⟨l, rfl⟩

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
  (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
  (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
  (hd0 : d.line (stdFullLattice ℚ_[p]) =
    Submodule.span κ {(0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
  (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
    (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
      (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)

include hg hd1 in

theorem one_tmul_not_mem_line_Lg (v : ↥(Lg p g).1) (hv : (v : Fin 2 → ℚ_[p]) ∉ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    (1 : κ) ⊗ₜ[ℤ_[p]] v ∉ d.line (Lg p g) := by
  intro hmem
  rw [d.homothety, hd1, Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton] at hmem
  obtain ⟨w, hvw, hw⟩ := exists_eq_act_tmul p (κ := κ) (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice ℚ_[p])) v
  obtain ⟨s, hws, hs⟩ := exists_eq_act_tmul p (κ := κ) g (stdFullLattice ℚ_[p]) w
  rw [hw 1, hs 1] at hmem
  have h1 := mem_span_of_equiv_mem (κ := κ) _ _ _ (mem_span_of_equiv_mem (κ := κ) _ _ _ hmem)
  refine one_tmul_not_mem_span_of_coordRed_eq_zero p 1 _ (coordRed_gen1 p) s ?_ h1
  rintro ⟨c, hc⟩
  apply hv
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have : (v : Fin 2 → ℚ_[p]) = fun i => algebraMap ℤ_[p] ℚ_[p] (![intCoord p s 0, c] i) := by
    rw [hvw, hws, scalarGL_mulVec, g_mulVec p g hg, coe_eq_intCoord p s]
    funext i; fin_cases i <;> simp [Units.val_inv_eq_inv_val, coe_pu, hc, map_mul, inv_mul_cancel_left₀ hp0]
  rw [this]; exact vec_mem_std p _

include hg hd0 in

theorem one_tmul_not_mem_line_std (v' : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (hv' : ¬ ∃ w : ↥(Lg p g).1, (v' : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • (w : Fin 2 → ℚ_[p])) :
    (1 : κ) ⊗ₜ[ℤ_[p]] v' ∉ d.line (stdFullLattice ℚ_[p]) := by
  rw [hd0]
  refine one_tmul_not_mem_span_of_coordRed_eq_zero p 0 _ (coordRed_gen0 p) v' ?_
  rintro ⟨c, hc⟩
  apply hv'
  refine ⟨⟨![algebraMap ℤ_[p] ℚ_[p] c, (((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℤ_[p] ℚ_[p] (intCoord p v' 1)],
    (mem_Lg_iff p g hg _).mpr ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (![c, intCoord p v' 1] i), vec_mem_std p _⟩, ?_⟩⟩, ?_⟩
  · funext i; fin_cases i <;> simp
  · have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    rw [coe_eq_intCoord p v']
    funext i; fin_cases i <;> simp [hc, map_mul, Units.val_inv_eq_inv_val, coe_pu, mul_inv_cancel_left₀ hp0]

include hg hd0 hd1 in

theorem edgeNondegAt_node (x : PrimeSpectrum κ) :
    d.EdgeNondegAt (p : ℤ_[p]) x.asIdeal (stdFullLattice ℚ_[p]) (Lg p g) := by
  refine ⟨std_le_Lg p g hg, fun v => smul_mem_std_of_mem_Lg p g hg v v.2, ?_, ?_⟩
  · intro v hv hmem
    rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq] at hmem
    exact one_tmul_not_mem_line_Lg p g hg d hd1 v hv hmem
  · intro v' hv' hmem
    rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq] at hmem
    exact one_tmul_not_mem_line_std p g hg d hd0 v' hv' hmem

end Node3

end B25N3

namespace B25N3

section SubIndex

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {π : R}

theorem eq_of_le_of_hasDetIndex {L L' : Submodule R (Fin 2 → K)} (hle : L ≤ L') {e : ℤ}
    (h : HasDetIndex π L e) (h' : HasDetIndex π L' e) : L = L' := by
  obtain ⟨g₁, rfl, u₁, hu₁⟩ := h
  obtain ⟨g₂, rfl, u₂, hu₂⟩ := h'

  have hk : latticeMap (g₂⁻¹ * g₁) (stdLattice R K) ≤ stdLattice R K := by
    rw [latticeMap_mul]
    have := latticeMap_mono g₂⁻¹ hle
    rwa [latticeMap_inv_latticeMap] at this
  have hcol : ∀ i j, IsLocalization.IsInteger R (((g₂⁻¹ * g₁ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) i j) := by
    intro i j
    have hj := hk (mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)) i
    rwa [mulVec_single_one] at hj
  choose a ha using fun q : Fin 2 × Fin 2 => hcol q.1 q.2
  set A : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => a (i, j) with hA
  have hmapA : (algebraMap R K).mapMatrix A = ((g₂⁻¹ * g₁ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) := by
    ext i j; exact ha (i, j)

  have hπ0 : algebraMap R K π ^ e ≠ 0 := by
    intro h0
    have := hu₁ ▸ (Matrix.GeneralLinearGroup.det g₁).ne_zero
    exact this (by rw [h0, mul_zero])
  have hu20 : algebraMap R K u₂ ≠ 0 := fun h0 => u₂.ne_zero (IsFractionRing.injective R K (by rw [h0, map_zero]))
  have hdetK : algebraMap R K A.det = algebraMap R K (u₁ * u₂⁻¹ : Rˣ) := by
    rw [RingHom.map_det, hmapA, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, hu₁, hu₂, Units.val_mul, map_mul, map_units_inv]
    field_simp
  have hdet : IsUnit A.det := by
    rw [IsFractionRing.injective R K hdetK]; exact Units.isUnit _
  obtain ⟨Au, hAu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  have hrange : (g₂⁻¹ * g₁) ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
    refine ⟨Au, Units.ext ?_⟩
    rw [← hmapA, ← hAu]; rfl
  have hfix := (latticeMap_stdLattice_eq_iff_mem_range _).mpr hrange
  rw [latticeMap_mul] at hfix
  have := congrArg (latticeMap g₂) hfix
  rwa [latticeMap_latticeMap_inv] at this

end SubIndex

end B25N3

namespace B25N3

section Node5

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
  (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
  (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
  (hd0 : d.line (stdFullLattice ℚ_[p]) =
    Submodule.span κ {(0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
  (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
    (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
      (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)

theorem hp_unit_false {c : ℤ_[p]} (h : (p : ℤ_[p]) * c = 1) : False :=
  PadicInt.irreducible_p.not_isUnit (IsUnit.of_mul_eq_one _ h)

include hg in
theorem hasDetIndex_Lg : HasDetIndex (p : ℤ_[p]) (Lg p g).1 (-1) := by
  refine ⟨scalarGL (pu p)⁻¹ * g, (latticeMap_mul _ _ _), 1, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    scalarGL_coe, hg, Matrix.det_smul, Matrix.det_one, Matrix.det_diagonal, Units.val_one, map_one, one_mul,
    zpow_neg_one, ← coe_pu, Units.val_inv_eq_inv_val, Fintype.card_fin]
  simp [Fin.prod_univ_two]
  field_simp

include hd0 in
theorem not_vertexNondegAt_std (x : PrimeSpectrum κ) : ¬ d.VertexNondegAt (p : ℤ_[p]) x.asIdeal (stdFullLattice ℚ_[p]) := by
  intro hV
  apply hV (stdBasisVec ℚ_[p] 1)
  · rintro ⟨w, hw⟩
    have hw' : stdBasisVec ℚ_[p] 1 = (p : ℤ_[p]) • w :=
      Subtype.ext (by rw [hw, Submodule.coe_smul, algebraMap_smul])
    have := congrArg (fun v => intCoord p v 1) hw'
    simp only [intCoord_stdBasisVec, intCoord_smul, if_true] at this
    exact hp_unit_false p this.symm
  · rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq, hd0, TensorProduct.zero_tmul, zero_add]
    exact Submodule.mem_span_singleton_self _

noncomputable def e0Lg (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1]) :
    ↥(Lg p g).1 := ⟨stdBasisVec ℚ_[p] 0, std_le_Lg p g hg (stdBasisVec ℚ_[p] 0).2⟩

include hg hd1 in
theorem not_vertexNondegAt_Lg (x : PrimeSpectrum κ) : ¬ d.VertexNondegAt (p : ℤ_[p]) x.asIdeal (Lg p g) := by
  intro hV
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply hV (e0Lg p g hg)
  · rintro ⟨w, hw⟩
    obtain ⟨s, hs⟩ := (mem_Lg_iff p g hg _).mp w.2
    have h0 := congrFun hw 0
    rw [hs, coe_eq_intCoord p s] at h0
    change (Pi.single (0 : Fin 2) (1 : ℚ_[p]) : Fin 2 → ℚ_[p]) 0 = _ at h0
    simp only [Pi.single_eq_same, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, ← map_mul] at h0
    exact hp_unit_false p (IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [map_one]; exact h0.symm))
  · rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq, d.homothety, hd1, Submodule.map_span, Submodule.map_span,
      Set.image_singleton, Set.image_singleton, TensorProduct.zero_tmul, add_zero]
    have : ((actBaseChange κ (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice ℚ_[p]))).toLinearMap
        ((actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap ((1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0))) =
        (1 : κ) ⊗ₜ[ℤ_[p]] e0Lg p g hg := by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, actBaseChange_tmul]
      erw [actBaseChange_tmul]
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, scalarGL_mulVec, g_mulVec p g hg]
      have hb : ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) = Pi.single 0 1 := rfl
      show _ = (Pi.single (0 : Fin 2) (1 : ℚ_[p]) : Fin 2 → ℚ_[p])
      rw [hb]
      funext i; fin_cases i <;> simp [Units.val_inv_eq_inv_val, coe_pu, inv_mul_cancel_left₀ hp0]
    rw [this]
    exact Submodule.mem_span_singleton_self _

include hg hd0 in

theorem mem_Lg_of_tmul_smul_mem (w : Fin 2 → ℚ_[p])
    (hw : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w ∈ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (h : (1 : κ) ⊗ₜ[ℤ_[p]] (⟨_, hw⟩ : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) ∈ d.line (stdFullLattice ℚ_[p])) :
    w ∈ (Lg p g).1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [hd0] at h
  by_cases hdiv : (p : ℤ_[p]) ∣ intCoord p ⟨_, hw⟩ 0
  · obtain ⟨c, hc⟩ := hdiv
    rw [mem_Lg_iff p g hg]
    refine ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (![c, intCoord p ⟨_, hw⟩ 1] i), vec_mem_std p _⟩, ?_⟩
    set a := intCoord p ⟨_, hw⟩ with ha
    have key : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w = fun i => algebraMap ℤ_[p] ℚ_[p] (a i) :=
      coe_eq_intCoord p ⟨_, hw⟩
    have hp0' : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by rw [← coe_pu]; exact (pu p).ne_zero
    apply smul_right_injective (Fin 2 → ℚ_[p]) hp0'
    beta_reduce
    rw [key]
    funext i; fin_cases i <;> simp [hc, map_mul, Units.val_inv_eq_inv_val, coe_pu, mul_inv_cancel_left₀ hp0]
  · exact (one_tmul_not_mem_span_of_coordRed_eq_zero p 0 _ (coordRed_gen0 p) _ hdiv h).elim

theorem line_map_Lg (c' : κ) (L : FullLattice ℤ_[p] ℚ_[p]) (x : PrimeSpectrum κ) (h₁ : L.1 = (Lg p g).1)
    (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
      (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
        (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap) :
    (d.map (p : ℤ_[p]) (toLocRing κ x)).line L = Submodule.span (locRing κ x)
      {transportEquiv (locRing κ x) (M₁ := Lg p g) (M₂ := L) h₁.symm
        (actBaseChange (locRing κ x) (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice ℚ_[p]))
          (actBaseChange (locRing κ x) g (stdFullLattice ℚ_[p])
            ((1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 +
              algebraMap κ (locRing κ x) c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by
  have ht := DeligneDatum.line_transport (π := (p : ℤ_[p])) d (M₁ := Lg p g) (M₂ := L) h₁.symm
  show lineBaseChange (toLocRing κ x) L (d.line L) = _
  rw [ht, d.homothety, hd1, Submodule.map_span, Set.image_singleton, Submodule.map_span, Set.image_singleton,
    Submodule.map_span, Set.image_singleton, lineBaseChange_span_singleton]
  congr 2
  show LinearMap.rTensor _ (toLocRing κ x).toLinearMap (transportEquiv κ h₁.symm (actBaseChange κ _ _ (actBaseChange κ _ _ _))) = _
  rw [rTensor_transportEquiv, rTensor_actBaseChange, rTensor_actBaseChange, map_add, LinearMap.rTensor_tmul,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]
  rfl

end Node5

end B25N3

namespace B25N3

section Eta

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem one_tmul_not_mem_span' (c' : κ) (hc' : c' ^ p ≠ c') (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (hw : ¬ ∀ i, (p : ℤ_[p]) ∣ intCoord p w i) :
    (1 : κ) ⊗ₜ[ℤ_[p]] w ∉ Submodule.span κ
      {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} := by
  intro h
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp h
  have g0 : coordRed p (κ := κ) 0 ((1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = 1 := by
    rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]; simp
  have g1 : coordRed p (κ := κ) 1 ((1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) = c' := by
    rw [map_add, coordRed_tmul, coordRed_tmul, intCoord_stdBasisVec, intCoord_stdBasisVec]; simp
  have e0 : l = algebraMap ℤ_[p] κ (intCoord p w 0) := by
    have := congrArg (coordRed p (κ := κ) 0) hl
    rwa [map_smul, g0, coordRed_tmul, one_mul, smul_eq_mul, mul_one] at this
  have e1 : l * c' = algebraMap ℤ_[p] κ (intCoord p w 1) := by
    have := congrArg (coordRed p (κ := κ) 1) hl
    rwa [map_smul, g1, coordRed_tmul, one_mul, smul_eq_mul] at this
  have h0 := algebraMap_pow_p p (κ := κ) (intCoord p w 0)
  have h1 := algebraMap_pow_p p (κ := κ) (intCoord p w 1)
  rw [← e0] at h0
  rw [← e1, mul_pow, h0] at h1

  have hl0 : l = 0 := by
    by_contra hne
    exact hc' (mul_left_cancel₀ hne h1)
  have d0 : (p : ℤ_[p]) ∣ intCoord p w 0 := dvd_of_algebraMap_eq_zero p (κ := κ) (by rw [← e0, hl0])
  have d1 : (p : ℤ_[p]) ∣ intCoord p w 1 := dvd_of_algebraMap_eq_zero p (κ := κ) (by rw [← e1, hl0, zero_mul])
  exact hw (fun i => by fin_cases i <;> first | exact d0 | exact d1)

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
  (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
  (c' : κ) (hc' : c' ^ p ≠ c') (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
  (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
    (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
      (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)

include hg hc' hd1 in

theorem vertexNondegAt_Lg (x : PrimeSpectrum κ) : d.VertexNondegAt (p : ℤ_[p]) x.asIdeal (Lg p g) := by
  intro v hv hmem
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [asIdeal_eq_bot, Submodule.bot_smul, sup_bot_eq, d.homothety, hd1, Submodule.map_span, Submodule.map_span,
    Set.image_singleton, Set.image_singleton] at hmem
  obtain ⟨w, hvw, hw⟩ := exists_eq_act_tmul p (κ := κ) (scalarGL (pu p)⁻¹) (FullLattice.act g (stdFullLattice ℚ_[p])) v
  obtain ⟨s, hws, hs⟩ := exists_eq_act_tmul p (κ := κ) g (stdFullLattice ℚ_[p]) w
  rw [hw 1, hs 1] at hmem
  have h1 := mem_span_of_equiv_mem (κ := κ) _ _ _ (mem_span_of_equiv_mem (κ := κ) _ _ _ hmem)
  refine one_tmul_not_mem_span' p c' hc' s ?_ h1
  intro hall
  obtain ⟨c0, hc0⟩ := hall 0
  obtain ⟨c1, hc1⟩ := hall 1
  apply hv
  refine ⟨⟨![algebraMap ℤ_[p] ℚ_[p] c0, (((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℤ_[p] ℚ_[p] c1],
    (mem_Lg_iff p g hg _).mpr ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (![c0, c1] i), vec_mem_std p _⟩, ?_⟩⟩, ?_⟩
  · funext i; fin_cases i <;> simp
  · show (v : Fin 2 → ℚ_[p]) = _
    rw [hvw, hws, scalarGL_mulVec, g_mulVec p g hg, coe_eq_intCoord p s]
    funext i; fin_cases i <;>
      simp [hc0, hc1, map_mul, Units.val_inv_eq_inv_val, coe_pu, inv_mul_cancel_left₀ hp0, mul_inv_cancel_left₀ hp0, mul_left_comm]

include hg hc' hd1 in

theorem edgeNondegAt_Lg_Lg (x : PrimeSpectrum κ) : d.EdgeNondegAt (p : ℤ_[p]) x.asIdeal (Lg p g) (Lg p g) := by
  refine ⟨le_rfl, fun v => ?_, fun v hv => (hv v.2).elim, vertexNondegAt_Lg p g hg c' hc' d hd1 x⟩
  rw [algebraMap_smul]; exact (Lg p g).1.smul_mem _ v.2

end Eta

end B25N3

open B25A B25N3 in
theorem solution
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (c' : κ) (hc' : c' ^ p ≠ c')
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
      (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
        (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ) :
    Q.IsQuadrupleOf d ↔
      ∃ (h₀ : Q.N₀ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1)
        (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1),
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x)
              (M₁ := (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])))) (M₂ := Q.L₀ x) h₀.symm
            (actBaseChange (locRing κ x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing κ x) g (stdFullLattice ℚ_[p])
                ((1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + algebraMap κ (locRing κ x) c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x)
              (M₁ := (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])))) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing κ x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing κ x) g (stdFullLattice ℚ_[p])
                ((1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + algebraMap κ (locRing κ x) c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by
  have hπ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have hπx : algebraMap ℤ_[p] κ (p : ℤ_[p]) ∈ x.asIdeal := by rw [algebraMap_p_eq_zero]; exact x.asIdeal.zero_mem
  have hπu : B25A.πu (K := ℚ_[p]) hπ = pu p := Units.ext rfl
  constructor
  · intro hQ
    have hV := vertexNondegAt_Lg p g hg c' hc' d hd1 x
    have idxLg := hasDetIndex_Lg p g hg
    have cov := stratum_cover Q x hπx
    have h₀₁ : Q.N₀ x = (Lg p g).1 ∧ Q.N₁ x = (Lg p g).1 := by
      by_cases hS1 : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule κ Q.T₀)
      · by_cases hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule κ Q.T₁)
        · exact (false_of_vertex_edge hπ d x hπx Q hQ (Lg p g) hV hS0 hS1).elim
        ·
          have h1 := N₀_eq_of_not_S₀ Q x hS0
          have hVQ := vertexNondegAt_L₀_of_V1 Q d hQ x h1
          obtain ⟨c₁, hc₁⟩ :=
            CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
              hπ d x.asIdeal hπx (Lg p g) (Q.L₀ x) (Q.L₁ x) hV (hQ x).1
          have hc₁' : latticeMap (scalarGL c₁) (Lg p g).1 = Q.N₁ x := by
            rcases hc₁ with hc₁ | hc₁
            · exact hc₁.trans h1
            · exact hc₁
          have idx1 := Q.hasDetIndex₁ x hS1
          have key := CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c₁ (-1) idxLg (hc₁'.symm ▸ idx1)
          have hN1 : Q.N₁ x = (Lg p g).1 := by rw [← hc₁', key]
          exact ⟨h1.trans hN1, hN1⟩
      ·
        have hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule κ Q.T₁) := cov.elim id (fun h => (hS1 h).elim)
        have h0 := N₀_eq_of_not_S₁ hπ Q x hS1
        have hVQ := vertexNondegAt_L₁_of_V0 hπ Q d hQ x h0
        have idx0 := Q.hasDetIndex₀ x hS0
        obtain ⟨c₁, hc₁⟩ :=
          CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
            hπ d x.asIdeal hπx (Lg p g) (Q.L₀ x) (Q.L₁ x) hV (hQ x).1
        rcases hc₁ with hc₁ | hc₁
        · change latticeMap (scalarGL c₁) (Lg p g).1 = Q.N₀ x at hc₁
          exact (not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ c₁ (-1) 0
            idxLg (hc₁.symm ▸ idx0)) (Or.inr (by norm_num))).elim
        · change latticeMap (scalarGL c₁) (Lg p g).1 = Q.N₁ x at hc₁
          have h0' : Q.N₀ x = latticeMap (scalarGL (B25A.πu (K := ℚ_[p]) hπ * c₁)) (Lg p g).1 := by
            rw [h0, ← hc₁, ← latticeMap_mul, ← scalarGL_mul]
          exact (not_even_one_aux (CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ _ (-1) 0
            idxLg (h0' ▸ idx0)) (Or.inr (by norm_num))).elim
    obtain ⟨h₀, h₁⟩ := h₀₁
    refine ⟨h₀, h₁, ?_, ?_⟩
    · rw [(hQ x).2.1, line_map_Lg p g d c' (Q.L₀ x) x h₀ hd1]
    · rw [(hQ x).2.2, line_map_Lg p g d c' (Q.L₁ x) x h₁ hd1]
  · rintro ⟨h₀, h₁, hk₀, hk₁⟩ x'
    rw [show x' = x from Subsingleton.elim _ _]
    refine ⟨?_, ?_, ?_⟩
    · have hL0 : Q.L₀ x = Lg p g := Subtype.ext h₀
      have hL1 : Q.L₁ x = Lg p g := Subtype.ext h₁
      rw [hL0, hL1]
      exact edgeNondegAt_Lg_Lg p g hg c' hc' d hd1 x
    · rw [hk₀, line_map_Lg p g d c' (Q.L₀ x) x h₀ hd1]
    · rw [hk₁, line_map_Lg p g d c' (Q.L₁ x) x h₁ hd1]

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_act_eq_span_of_pow_ne
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_act_eq_span_of_pow_ne (solution)
