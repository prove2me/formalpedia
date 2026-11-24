-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_LMR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:12:31.887899+00:00
-- url     : https://prove2.me/submissions/e694381c-9ce6-44cb-9cb2-482a69600dac

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_rel
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_Md
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_fac_list
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Rep_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section Bridge
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
private theorem rep_zero_lemma_2 (d : ℕ) : Rep d (0 : AA k r E) :=
  ⟨[], by simp, fun _ _ => by simp⟩
private theorem ckOn_mono_lemma_4 {m m' : ℕ∞} (h : m' ≤ m) {f : Mat k r → E} (hf : CkOn m (GV k r) f) :
    CkOn m' (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr h), heq⟩
end Bridge
section Skew
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
private theorem fw_local_lemma_7 (hL : HL Eop) (w : List (Ix k r)) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, Fw Eop w f g = Fw Eop w f₂ g := by
  induction w with
  | nil => simpa [Fw] using h
  | cons x w ih =>
    intro g hg
    simp only [Fw, List.foldr_cons] at ih ⊢
    exact hL _ _ _ _ ih g hg
private theorem ev_local_lemma_8 (hL : HL Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, ev Eop a f g = ev Eop a f₂ g := by
  intro g hg
  obtain ⟨L, -, hLa⟩ := ha
  simp only [ev, hLa, Phi, List.nil_append]
  have key : ∀ L' : List (ℂ × List (Ix k r)),
      (L'.map fun p => p.1 • Fw Eop p.2 f).sum g = (L'.map fun p => p.1 • Fw Eop p.2 f₂).sum g := by
    intro L'
    induction L' with
    | nil => simp
    | cons p L' ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, ih,
        fw_local_lemma_7 Eop hL p.2 f f₂ h g hg]
  exact key L
private theorem rep_list_lemma_9 : ∀ l : List (AA k r E), (∀ x ∈ l, Rep 1 x) → Rep l.length l.prod := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons x l ih =>
    intro h
    rw [List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega)
      (rep_mul (h x (by simp)) (ih fun y hy => h y (by simp [hy])))
end Skew
section Ad
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Ad
end Formalism.FourierDecayAlt.P.JFxE
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) f g = 0 := by
  intro g hg
  unfold Lt Rt
  have h0 : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hadd : ∀ (x y : AA k r E) (φ : Mat k r → E) (g' : Mat k r),
      ev Eop (x + y) φ g' = ev Eop x φ g' + ev Eop y φ g' := by
    intro x y φ g'
    simp [ev]
  have hL1 := rep_fac_list (k := k) (r := r) (E := E) a b u σ
  set L := List.ofFn (fac (Lf k r E) a b u σ) with hLdef
  have hLt := rep_list_lemma_9 (L.take i) (fun x hx => hL1 x (List.mem_of_mem_take hx))
  have hRt := rep_list_lemma_9 (L.drop ((i : ℕ) + 2)) (fun x hx => hL1 x (List.mem_of_mem_drop hx))
  have hMd := rep_Md (k := k) (r := r) (E := E) a b σ i
  have hlen : (L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length = m + 1 := by
    have := i.isLt
    simp only [hLdef, List.length_take, List.length_drop, List.length_ofFn]
    omega
  have hf3 : CkOn (((L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length : ℕ) : ℕ∞) (GV k r) f := by
    rw [hlen]
    exact hf
  have hψ : CkOn (((L.take i).length + 2 : ℕ) : ℕ∞) (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) :=
    ev_ck (Eop := Eop) hC hRt _ f hf3
  have hψ2 : CkOn 2 (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) := by
    have := ev_ck (Eop := Eop) hC hRt 2 f (ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by omega)) hf3)
    simpa using this
  have hz : ∀ g' ∈ GV k r,
      ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) g' = 0 := by
    intro g' hg'
    unfold Md
    rw [hadd, ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg', ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg',
      add_zero]
  rw [ev_mul (Eop := Eop) hC hL hA hS (rep_mul hLt hMd) hRt f hf3 g hg,
    ev_mul (Eop := Eop) hC hL hA hS hLt hMd _ hψ g hg,
    ev_local_lemma_8 Eop hL hLt (ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (ev Eop (0 : AA k r E) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (fun g' hg' => by simp [hz g' hg', h0]) g hg,
    ← ev_mul (Eop := Eop) hC hL hA hS hLt (rep_zero_lemma_2 2) _ hψ g hg]
  simp [h0]
end Formalism.FourierDecayAlt.P.JFxE
