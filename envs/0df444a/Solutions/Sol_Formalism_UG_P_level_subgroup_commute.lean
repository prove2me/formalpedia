-- Prove2me | solution 1 for Formalism.UG.P.level_subgroup_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:41.385366+00:00
-- url     : https://prove2.me/submissions/d9197850-8489-4a63-990a-753ca478b0c6

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_relIndex_ne_zero
import Theorems.Thm_Formalism_UG_P_levelv_denom_family
import Theorems.Thm_Formalism_UG_P_levelv_smul_mulVec_mem
import Theorems.Thm_Formalism_UG_P_levelv_phi_mem
import Theorems.Thm_Formalism_UG_P_levelv_lat_phi
import Theorems.Thm_Formalism_UG_P_levelv_nsmul_inj
import Theorems.Thm_Formalism_UG_P_levelv_mulVec_inv
import Theorems.Thm_Formalism_UG_P_levelv_stab_of_eq
import Theorems.Thm_Formalism_UG_P_glint_finite_quotient_of_dvr
import Theorems.Thm_Formalism_UG_P_glint_finite_residueField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.LevelVComm := by
  intro F E _ _ _ _ _ n _ _ σ J v g
  classical
  have hlev : ∀ k : UPts σ J (v.adicCompletion F),
      k ∈ (levelV σ J v).subgroupOf (UPts σ J (v.adicCompletion F)) ↔
        (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    simp only [levelV, level, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  obtain ⟨N, hN0, hN⟩ := levelv_denom_family (E := E) v (fun p : (n × n) ⊕ (n × n) =>
    Sum.elim (fun q : n × n => ((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) q.1 q.2)
      (fun q : n × n => (((g : GL n (E ⊗[F] v.adicCompletion F))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) q.1 q.2) p)
  have hg : ∀ i j, N • ((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈ lvS F E v :=
    fun i j => hN (.inl (i, j))
  have hg' : ∀ i j, N • (((g : GL n (E ⊗[F] v.adicCompletion F))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
      lvS F E v :=
    fun i j => hN (.inr (i, j))
  obtain ⟨c, hcdef⟩ : ∃ c : v.adicCompletionIntegers F, c = ((N * N : ℕ) : v.adicCompletionIntegers F) :=
    ⟨_, rfl⟩
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    rw [hcdef] at h1
    simp [hN0] at h1
  have : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    glint_finite_quotient_of_dvr (glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let Z : UPts σ J (v.adicCompletion F) → Set (n → E ⊗[F] v.adicCompletion F) := fun k =>
    (fun x => N • (((k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
      (((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ x))) ''
      (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) : Set (n → E ⊗[F] v.adicCompletion F))
  have hZ1 : ∀ k : UPts σ J (v.adicCompletion F),
      (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
        Z k ⊆ (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) : Set (n → E ⊗[F] v.adicCompletion F)) := by
    rintro k hk _ ⟨x, hx, rfl⟩
    simp only
    rw [← Matrix.mulVec_smul]
    exact (hk _).1 (levelv_smul_mulVec_mem v N _ hg x hx)
  have hZ2 : ∀ k : UPts σ J (v.adicCompletion F),
      (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
        ∀ z ∈ stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v), (N * N) • z ∈ Z k := by
    intro k hk z hz
    have hw : ((((k : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) := ((inv_mem hk) z).1 hz
    refine ⟨N • ((((g : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
      (((((k : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z),
      levelv_smul_mulVec_mem v N _ hg' _ hw, ?_⟩
    simp only
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, levelv_mulVec_inv, levelv_mulVec_inv, mul_smul]
  have hZ3 : ∀ k : UPts σ J (v.adicCompletion F), ∀ y ∈ Z k, ∀ y' ∈ Z k, y + y' ∈ Z k := by
    rintro k _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact ⟨x + x', add_mem hx hx', by simp only [Matrix.mulVec_add, smul_add]⟩
  let π : (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →
      (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    fun α j i => Ideal.Quotient.mk _ (α j i)
  let f : UPts σ J (v.adicCompletion F) →
      Set (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    fun k => π '' ((levelvPhi F E v n) ⁻¹' Z k)
  have hsub : ∀ a b : UPts σ J (v.adicCompletion F),
      (a : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
      (b : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) → f a = f b → Z a ⊆ Z b := by
    intro a b ha hb hab y hy
    obtain ⟨α, hα⟩ := levelv_lat_phi v y (hZ1 a ha hy)
    have hmem : π α ∈ f b := by
      rw [← hab]
      exact ⟨α, by rw [Set.mem_preimage, hα]; exact hy, rfl⟩
    obtain ⟨α', hα'Z, hπ⟩ := hmem
    have hdiff : ∀ j i, α j i - α' j i ∈ Ideal.span {c} := by
      intro j i
      have := congrFun (congrFun hπ j) i
      exact Ideal.Quotient.eq.1 this.symm
    choose β hβ using fun j i => Ideal.mem_span_singleton'.1 (hdiff j i)
    have hαβ : α = α' + (N * N) • β := by
      funext j i
      have := hβ j i
      rw [hcdef] at this
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul]
      push_cast at this ⊢
      linear_combination -this
    rw [← hα, hαβ, map_add, map_nsmul]
    exact hZ3 b _ hα'Z _ (hZ2 b hb _ (levelv_phi_mem v β))
  refine levelv_relIndex_ne_zero _ _ f ?_
  intro a ha b hb hab
  have ha' := (hlev a).1 ha
  have hb' := (hlev b).1 hb
  have hZ : Z a = Z b := (hsub a b ha' hb' hab).antisymm (hsub b a hb' ha' hab.symm)
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hlev]
  intro x
  exact levelv_stab_of_eq _ N (levelv_nsmul_inj v hN0) _ _ _ hZ x
end Formalism.UG.P
