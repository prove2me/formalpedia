-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.frames_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:31.916866+00:00
-- url     : https://prove2.me/submissions/c5f835be-ca3a-4149-91bf-e2f3f3da3873

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_vi_mem_hat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_vi_add_smul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_vi_smul_int
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_incl_int_mem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_gmv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_approx_hat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_hat_fwd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_hat_iff
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_dl_anti
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_dl_map
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_bc_mem_UPts
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_dl_le
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hat_mono
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_glob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Lb : Submodule (𝓞 E) (n → E))
    (hLbd : IsLat (dl σ J Lb)) {cls : Type} (Λ : cls → Submodule (𝓞 E) (n → E))
    (hΔ : ∀ c, IsLat (dl σ J (Λ c))) (y : cls → GL n 𝒜)
    (hy : ∀ c, y c ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ c (u : n → 𝒜), u ∈ hat F (Λ c) ↔ (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb)
    (M : ℕ) (hM : M ≠ 0) {m : Type} [Fintype m] (b : m → n → E) (hb : ∀ a, b a ∈ dl σ J Lb)
    (hgen : ∀ x ∈ dl σ J Lb, ∃ r : m → 𝓞 E, ∃ z ∈ dl σ J Lb, x = ∑ a, r a • b a + (M : E) • z) :
    ∃ e : cls → m → n → E, (∀ c a, e c a ∈ dl σ J (Λ c)) ∧
      ∀ c c' (G : GL n E), G ∈ UJ (σ : E →+* E) J →
        (∀ x, x ∈ Λ c ↔ (G : Matrix n n E) *ᵥ x ∈ Λ c') →
        (∀ a, ∃ w ∈ dl σ J (Λ c'), (G : Matrix n n E) *ᵥ e c a - e c' a = (M : E) • w) →
        ∃ k : GL n 𝒜, k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
          (∀ u : n → 𝒜, u ∈ hat F Lb ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb) ∧
          (∀ u ∈ hat F (dl σ J Lb), ∃ z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z) ∧
          y c' = bc ιA G * y c * k⁻¹ := by

  have hya : ∀ c (w : n → 𝒜), w ∈ hat F (dl σ J Lb) → ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (dl σ J (Λ c)) := by
    intro c w hw
    have h1 : Λ c ≤ globLat (y c) Lb := fun x hx => (hyl c _).1 (vi_mem_hat hx)
    have h2 : globLat (y c) (dl σ J Lb) ≤ dl σ J (Λ c) :=
      (glob_dl_le σ J Lb (y c) (hy c)).trans (dl_anti σ J h1)
    have h3 : ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (globLat (y c) (dl σ J Lb)) := by
      rw [mem_hat_glob hLbd]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact hw
    exact hat_mono h2 h3

  have hyb : ∀ c (u : n → 𝒜), u ∈ hat F (dl σ J (Λ c)) →
      (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro c u hu
    have h1 : Lb ≤ globLat (y c)⁻¹ (Λ c) := by
      intro x hx
      show ((((y c)⁻¹)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F x ∈ hat F (Λ c)
      rw [inv_inv, hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact vi_mem_hat hx
    have h2 : globLat (y c)⁻¹ (dl σ J (Λ c)) ≤ dl σ J Lb :=
      (glob_dl_le σ J (Λ c) _ (inv_mem (hy c))).trans (dl_anti σ J h1)
    have h3 : (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (globLat (y c)⁻¹ (dl σ J (Λ c))) := by
      rw [mem_hat_glob (hΔ c), inv_inv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hu
    exact hat_mono h2 h3

  have hfr : ∀ c a, ∃ x ∈ dl σ J (Λ c), ∃ z ∈ hat F (dl σ J (Λ c)),
      ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) = vi F x + (M : 𝒜) • z :=
    fun c a => approx_hat M hM _ _ (hya c _ (vi_mem_hat (hb a)))
  choose e he z hz hez using hfr
  refine ⟨e, he, ?_⟩
  intro c c' G hG hGΛ hGe
  set k : GL n 𝒜 := (y c')⁻¹ * bc ιA G * y c with hk
  have hkm : (k : Matrix n n 𝒜) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * (G : Matrix n n E).map ιA *
      ((y c : GL n 𝒜) : Matrix n n 𝒜) := by
    rw [hk, Units.val_mul, Units.val_mul]; rfl
  have hGd := dl_map σ J G hG hGΛ

  have hkd : ∀ u ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro u hu
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hyb c' _ (hat_fwd _ hGd _ (hya c _ hu))

  have hkb : ∀ a, ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (b a) - vi F (b a) = (M : 𝒜) • Z := by
    intro a
    obtain ⟨w, hw, hwe⟩ := hGe a
    have hGe' : (G : Matrix n n E) *ᵥ e c a = e c' a + (M : E) • w := sub_eq_iff_eq_add'.1 hwe
    have key : (G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) -
        ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) =
        (M : 𝒜) • (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a) := by
      rw [hez c a, hez c' a, mulVec_add, mulVec_smul, gmv, hGe', vi_add_smul]
      simp only [smul_add, smul_sub]
      abel
    refine ⟨(((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a),
      hyb c' _ (sub_mem (add_mem (vi_mem_hat hw) (hat_fwd _ hGd _ (hz c a))) (hz c' a)), ?_⟩
    have h1 : vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        (((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have h2 : (k : Matrix n n 𝒜) *ᵥ vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) := by
      rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have h3 : (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) - vi F (b a) =
        (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ ((G : Matrix n n E).map ιA *ᵥ
          (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) - ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_sub, ← h1]
    rw [h2, h3, key, mulVec_smul]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem (hy c')) (bc_mem_UPts σ J G hG)) (hy c)
  · intro u
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have e1 : u ∈ hat F Lb ↔ ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (Λ c) := by
      rw [hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [e1, hat_iff G hGΛ, hyl]
  · intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      show ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z

      have hadd : ∀ x x' : n → E, (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x' - vi F x' = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (x + x') - vi F (x + x') = (M : 𝒜) • Z := by
        rintro x x' ⟨Z, hZ, hZe⟩ ⟨Z', hZ', hZe'⟩
        refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
        have : vi F (x + x') = vi F x + vi F x' := by funext i; simp [vi]
        rw [this, mulVec_add, smul_add, ← hZe, ← hZe']
        abel
      have hzero : ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (0 : n → E) - vi F 0 = (M : 𝒜) • Z :=
        ⟨0, zero_mem _, by
          have : vi F (0 : n → E) = 0 := by funext i; simp [vi]
          rw [this, mulVec_zero, sub_zero, smul_zero]⟩
      have hsmul : ∀ (r : 𝓞 E) (x : n → E),
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (r • x) - vi F (r • x) = (M : 𝒜) • Z := by
        rintro r x ⟨Z, hZ, hZe⟩
        refine ⟨(⟨_, incl_int_mem r⟩ : 𝒮) • Z, Submodule.smul_mem _ _ hZ, ?_⟩
        rw [vi_smul_int, mulVec_smul, ← smul_sub, hZe, Subring.smul_def, smul_comm]
      classical
      obtain ⟨r, z0, hz0, rfl⟩ := hgen x hx
      refine hadd _ _ ?_ ?_
      · have : ∀ s : Finset m, ∃ Z ∈ hat F (dl σ J Lb),
            (k : Matrix n n 𝒜) *ᵥ vi F (∑ a ∈ s, r a • b a) - vi F (∑ a ∈ s, r a • b a) = (M : 𝒜) • Z := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hzero
          | insert a s ha ih =>
            rw [Finset.sum_insert ha]
            exact hadd _ _ (hsmul _ _ (hkb a)) ih
        exact this Finset.univ
      · refine ⟨(k : Matrix n n 𝒜) *ᵥ vi F z0 - vi F z0, sub_mem (hkd _ (vi_mem_hat hz0)) (vi_mem_hat hz0), ?_⟩
        have : vi F ((M : E) • z0) = (M : 𝒜) • vi F z0 := by
          have := vi_add_smul (F := F) (0 : n → E) z0 M
          rwa [zero_add, show vi F (0 : n → E) = 0 from by funext i; simp [vi], zero_add] at this
        rw [this, mulVec_smul, smul_sub]
    | zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      obtain ⟨Z', hZ', hZe'⟩ := hw
      refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
      rw [mulVec_add, smul_add, ← hZe, ← hZe']
      abel
    | smul s u _ hu =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      refine ⟨s • Z, Submodule.smul_mem _ s hZ, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hZe, smul_comm]
  · rw [hk]
    group
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
