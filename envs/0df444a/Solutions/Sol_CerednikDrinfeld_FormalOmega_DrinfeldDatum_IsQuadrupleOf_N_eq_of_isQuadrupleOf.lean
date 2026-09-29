-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ea21c0df-e4de-521f-9e74-8877e42d5662

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
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

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

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

open B25A in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) (h' : Q'.IsQuadrupleOf d) :
    ∀ x : PrimeSpectrum B, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  intro x
  have hπx : algebraMap 𝒪 B π ∈ x.asIdeal := by
    obtain ⟨n, hn⟩ := hB
    exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  have cov := stratum_cover Q x hπx
  have cov' := stratum_cover Q' x hπx
  by_cases hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁) <;>
  by_cases hS1 : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀) <;>
  by_cases hS0' : LinearMap.range Q'.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q'.T₁) <;>
  by_cases hS1' : LinearMap.range Q'.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q'.T₀)

  · exact eq_of_E_E hπ d x hπx Q h Q' h' hS0 hS1 hS0' hS1'

  · exact (false_of_vertex_edge hπ d x hπx Q h (Q'.L₁ x)
      (vertexNondegAt_L₁_of_V0 hπ Q' d h' x (N₀_eq_of_not_S₁ hπ Q' x hS1')) hS0 hS1).elim

  · exact (false_of_vertex_edge hπ d x hπx Q h (Q'.L₀ x)
      (vertexNondegAt_L₀_of_V1 Q' d h' x (N₀_eq_of_not_S₀ Q' x hS0')) hS0 hS1).elim

  · exact (cov'.elim hS0' hS1').elim

  · exact (false_of_vertex_edge hπ d x hπx Q' h' (Q.L₁ x)
      (vertexNondegAt_L₁_of_V0 hπ Q d h x (N₀_eq_of_not_S₁ hπ Q x hS1)) hS0' hS1').elim

  · exact eq_of_V0_V0 hπ d x hπx Q h Q' h' hS0 (N₀_eq_of_not_S₁ hπ Q x hS1) hS0' (N₀_eq_of_not_S₁ hπ Q' x hS1')

  · exact (false_of_V0_V1 hπ d x hπx Q h Q' h' hS0 (N₀_eq_of_not_S₁ hπ Q x hS1) hS1' (N₀_eq_of_not_S₀ Q' x hS0')).elim
  · exact (cov'.elim hS0' hS1').elim

  · exact (false_of_vertex_edge hπ d x hπx Q' h' (Q.L₀ x)
      (vertexNondegAt_L₀_of_V1 Q d h x (N₀_eq_of_not_S₀ Q x hS0)) hS0' hS1').elim

  · exact (false_of_V0_V1 hπ d x hπx Q' h' Q h hS0' (N₀_eq_of_not_S₁ hπ Q' x hS1') hS1
      (N₀_eq_of_not_S₀ Q x hS0)).elim

  · exact eq_of_V1_V1 hπ d x hπx Q h Q' h' hS1 (N₀_eq_of_not_S₀ Q x hS0) hS1' (N₀_eq_of_not_S₀ Q' x hS0')
  · exact (cov'.elim hS0' hS1').elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf (solution)
