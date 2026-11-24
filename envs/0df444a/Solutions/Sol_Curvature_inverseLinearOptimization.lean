-- Prove2me | solution 1 for Curvature.inverseLinearOptimization
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:38:47.748219+00:00
-- url     : https://prove2.me/submissions/d18540c4-7647-40fb-ba17-921d34c124f7

import Definitions.Def_Curvature_InverseLinearActions
import Theorems.Thm_Curvature_adaptiveWidth

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


namespace AdaptiveBase
variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ} (P : AdaptiveWeightRule M)


theorem adaptivePlay_prefix (G : ℝ) (g g' : ℕ → Vec d) (t : ℕ)
    (heq : ∀ i < t, g i = g' i) :
    B.adaptivePlay hcv P G g t = B.adaptivePlay hcv P G g' t := by
  suffices B.adaptiveStateAfter hcv P G g t = B.adaptiveStateAfter hcv P G g' t
    by simp only [adaptivePlay, this]
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [adaptiveStateAfter, ih (fun i hi => heq i (by omega)), heq t (by omega)]

section Run
variable (G : ℝ) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G


end Run
end AdaptiveBase
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


theorem adaptiveWidthConstant_pos : 0 < adaptiveWidthConstant := by
  unfold adaptiveWidthConstant adaptiveBaseWidthFactor
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)} {G W : ℝ}


theorem InverseLinearActions.exists_optimal (X : InverseLinearActions d G) (w : Vec d) :
    ∃ a, X.Optimal w a := by
  have hc : Continuous (fun a : Vec d => dotProduct w a) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  obtain ⟨a, ha, hmax⟩ := X.compact.exists_isMaxOn X.nonempty hc.continuousOn
  exact ⟨a, ha, fun b hb => hmax hb⟩

def InverseLinearActions.maximizer (X : InverseLinearActions d G) (w : Vec d) : Vec d :=
  (X.exists_optimal w).choose

theorem InverseLinearActions.maximizer_optimal (X : InverseLinearActions d G) (w : Vec d) :
    X.Optimal w (X.maximizer w) :=
  (X.exists_optimal w).choose_spec


theorem InverseLinearActions.shortfall_eq {X : InverseLinearActions d G} {u a : Vec d}
    (ha : X.Optimal u a) (y : Vec d) : X.shortfall u y = dotProduct u (a-y) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  simp only [dotProduct_sub]
  exact sub_le_sub_right (ha.2 b hb) _

theorem InverseLinearActions.le_shortfall (X : InverseLinearActions d G) (u y : Vec d)
    {a : Vec d} (ha : a ∈ X.carrier) : dotProduct u (a-y) ≤ X.shortfall u y := by
  have hmax := X.maximizer_optimal u
  rw [X.shortfall_eq hmax y, dotProduct_sub, dotProduct_sub]
  exact sub_le_sub_right (hmax.2 a ha) _

theorem InverseLinearActions.shortfall_nonneg (X : InverseLinearActions d G) (u : Vec d)
    {y : Vec d} (hy : y ∈ X.carrier) : 0 ≤ X.shortfall u y := by
  simpa only [sub_self, dotProduct_zero] using X.le_shortfall u y hy

theorem InverseLinearActions.shortfall_subgradient {X : InverseLinearActions d G}
    {w a : Vec d} (ha : X.Optimal w a) (y u : Vec d) :
    X.shortfall w y - X.shortfall u y ≤ excess (a-y) w u := by
  rw [X.shortfall_eq ha y, excess, dotProduct_sub (a-y) w u, dotProduct_comm (a-y) w,
    dotProduct_comm (a-y) u]
  exact sub_le_sub_left (X.le_shortfall u y ha.1) _

section Protocol
variable (I : DomainInitialization K) (hc : IsCompact K) (hcv : Convex ℝ K) (hne : K.Nonempty)
  (P : AdaptiveWeightRule (adaptiveWidthScale G W))


theorem inverseLinearPredict_eq (g : ℕ → Vec d) (t : ℕ) :
    inverseLinearPredict I hc hcv hne P t (fun j => g j.val) =
      (I.adaptiveBase hne hc hcv).adaptivePlay hcv P G g t := by
  apply AdaptiveBase.adaptivePlay_prefix
  intro i hi
  simp [hi]


end Protocol
end Curvature
end
end

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}
variable {G W : ℝ}
variable (I : DomainInitialization K) (hc : IsCompact K) (hcv : Convex ℝ K) (hne : K.Nonempty)
  (P : AdaptiveWeightRule (adaptiveWidthScale G W))

theorem solution (hG : 0 < G) (hW : 0 < W) (hw : coordinateWidth K ≤ W)
    (X : ℕ → InverseLinearActions d G) (a y : ℕ → Vec d)
    (hy : ∀ t, y t ∈ (X t).carrier)
    (ha : ∀ t, (X t).Optimal (inverseLinearPredict I hc hcv hne P t
      (fun j => a j.val - y j.val)).val (a t))
    (T : ℕ) (hT : 0 < T) (u : K) :
    let D := ∑ t ∈ Finset.range T, (X t).shortfall u.val (y t)
    (∑ t ∈ Finset.range T, dotProduct u.val (y t-a t)) ≤
      adaptiveWidthConstant*(G*W + Real.sqrt (G*W*D)) := by
  let g := fun t => a t-y t
  let w := (I.adaptiveBase hne hc hcv).adaptivePlay hcv P G g
  let r := fun t => excess (g t) (w t).val u.val
  have hopt (t : ℕ) : (X t).Optimal (w t).val (a t) := by
    have h := ha t
    change (X t).Optimal (inverseLinearPredict I hc hcv hne P t (fun j => g j.val)).val (a t) at h
    rw [inverseLinearPredict_eq] at h
    exact h
  have hg (t : ℕ) : norm₂ (g t) ≤ G :=
    (X t).diameterBound (a t) (hopt t).1 (y t) (hy t)
  have hnonneg (t : ℕ) : 0 ≤ (X t).shortfall (w t).val (y t) :=
    (X t).shortfall_nonneg _ (hy t)
  have hregret (t : ℕ) :
      dotProduct u.val (y t-a t) = r t - (X t).shortfall (w t).val (y t) := by
    rw [(X t).shortfall_eq (hopt t) (y t)]
    simp only [r, g, excess, dotProduct_sub, sub_dotProduct]
    rw [dotProduct_comm (a t) (w t).val, dotProduct_comm (y t) (w t).val,
      dotProduct_comm (a t) u.val, dotProduct_comm (y t) u.val]
    ring
  have hobs : (∑ t ∈ Finset.range T, dotProduct u.val (y t-a t)) ≤
      ∑ t ∈ Finset.range T, r t := Finset.sum_le_sum fun t _ =>
    (hregret t).le.trans (sub_le_self _ (hnonneg t))
  have hD : adaptiveNegative T r ≤ ∑ t ∈ Finset.range T, (X t).shortfall u.val (y t) := by
    apply Finset.sum_le_sum
    intro t _
    have hsub := (X t).shortfall_subgradient (hopt t) (y t) u.val
    exact max_le ((X t).shortfall_nonneg u.val (hy t)) (by
      change (X t).shortfall (w t).val (y t) - (X t).shortfall u.val (y t) ≤ r t at hsub
      linarith only [hsub, hnonneg t])
  have hlin := (adaptiveWidth I hc hcv hne hG hW hw P g hg T hT u).1
  exact hobs.trans (hlin.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hD (mul_nonneg hG.le hW.le))))
    adaptiveWidthConstant_pos.le))
